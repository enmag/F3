from typing import Union, Generator, Tuple, Optional
from itertools import chain

from pysmt.environment import Environment as PysmtEnv
from pysmt.fnode import FNode
import pysmt.typing as types
from pysmt.exceptions import SolverReturnedUnknownResultError

from expr_at_time import ExprAtTime
from canonize import Canonizer
from generalise_path import Generaliser
from rationalapprox import RationalApprox, approximate
from efsolver import efsolve
from solver import get_solvers, Solver, solve_with_timeout
from motzkin import motzkin_transpose
from rewritings import TimesDistributor
from utils import to_next, log, to_smt2

PREF = "_rank"


def set_rf_timeout(val):
    RankingFunction.set_timeout(val)


def get_rf_timeout():
    return RankingFunction.get_timeout()


class Ranker:

    def __init__(self, env: PysmtEnv, td: TimesDistributor, cn: Canonizer):
        assert isinstance(env, PysmtEnv)
        self.env = env
        self.td = td
        self.cn = cn
        self.totime = ExprAtTime(env=env, ignore_pref=PREF)

    def get_rf(self, symbs: frozenset, abst_states: list,
               abst_trans: list, trans_eqs: Optional[list]):
        assert isinstance(symbs, frozenset)
        assert isinstance(abst_states, list)
        assert isinstance(abst_trans, list)
        assert trans_eqs is None or isinstance(trans_eqs, list)
        assert len(abst_states) == len(abst_trans) + 1
        assert trans_eqs is None or len(abst_trans) == len(trans_eqs)
        assert all(isinstance(s, FNode) for s in symbs)
        assert all(isinstance(c, (set, frozenset)) for c in abst_states)
        assert all(isinstance(c, (set, frozenset)) for c in abst_trans)
        assert trans_eqs is None or all(isinstance(c, dict) for c in trans_eqs)
        assert all(isinstance(c, FNode) for s in abst_states for c in s)
        assert all(isinstance(c, FNode) for s in abst_trans for c in s)
        assert trans_eqs is None or \
            all(isinstance(c, FNode) for eqs in trans_eqs for c in eqs.keys())
        assert trans_eqs is None or \
            all(c in self.env.formula_manager.formulae.values()
                for eqs in trans_eqs for c in eqs.keys())
        assert trans_eqs is None or \
            all(isinstance(c, FNode)
                for eqs in trans_eqs for c in eqs.values())
        assert trans_eqs is None or \
            all(c in self.env.formula_manager.formulae.values()
                for eqs in trans_eqs for c in eqs.values())
        assert all(s.is_symbol() for s in symbs)
        assert all(s in self.env.formula_manager.get_all_symbols()
                   for s in symbs)
        assert all(c in self.env.formula_manager.formulae.values()
                   for s in abst_states for c in s)
        assert all(c in self.env.formula_manager.formulae.values()
                   for s in abst_trans for c in s)
        mgr = self.env.formula_manager
        trans = [frozenset(chain(abst_t,
                                 (mgr.Equals(s, v) for s, v in eqs.items())))
                 for abst_t, eqs in zip(abst_trans, trans_eqs)] if trans_eqs \
            else abst_trans

        yield RankingFunction(self.env, symbs, abst_states,
                              trans, self.td, self.cn,
                              self.totime)


class RankingFunction:
    """Represents a ranking function"""

    _TIMEOUT = 25
    _LOG_LVL = 1

    @staticmethod
    def set_timeout(val: int) -> None:
        assert isinstance(val, int)
        RankingFunction._TIMEOUT = val

    @staticmethod
    def get_timeout() -> int:
        return RankingFunction._TIMEOUT

    def __init__(self, env: PysmtEnv, symbs: frozenset,
                 abst_states: list, abst_trans: list,
                 td: TimesDistributor, cn: Canonizer, totime: ExprAtTime):
        assert isinstance(env, PysmtEnv)
        assert isinstance(symbs, frozenset)
        assert isinstance(abst_states, list)
        assert isinstance(abst_trans, list)
        assert isinstance(td, TimesDistributor)
        assert isinstance(cn, Canonizer)
        assert isinstance(totime, ExprAtTime)
        assert len(abst_states) == len(abst_trans) + 1
        assert all(isinstance(s, FNode) for s in symbs)
        assert all(isinstance(c, (set, frozenset)) for c in abst_states)
        assert all(isinstance(c, (set, frozenset)) for c in abst_trans)
        assert all(isinstance(c, FNode) for s in abst_states for c in s)
        assert all(isinstance(c, FNode) for s in abst_trans for c in s)
        assert all(s.is_symbol() for s in symbs)
        assert all(s in env.formula_manager.get_all_symbols() for s in symbs)
        assert all(c in env.formula_manager.formulae.values()
                   for s in abst_states for c in s)
        assert all(c in env.formula_manager.formulae.values()
                   for s in abst_trans for c in s)
        assert len(abst_states) == len(abst_trans) + 1

        self.env = env
        mgr = self.env.formula_manager
        self.real_symbs = frozenset(s for s in symbs
                                    if s.symbol_type().is_real_type())
        self.int_symbs = frozenset(s for s in symbs
                                   if s.symbol_type().is_int_type())
        self.states = abst_states
        self.trans = abst_trans
        self.td = td
        self.cn = cn
        self.totime = totime

        mgr = self.env.formula_manager
        self.rf_expr, params = self._linear_comb(self.symbs_to_same_type)
        rf_type = self.env.stc.get_type(self.rf_expr)
        self.rf_zero = mgr.Int(0) if rf_type.is_int_type() else mgr.Real(0)
        self.rf_pred = self.cn(mgr.GT(self.rf_expr, self.rf_zero))
        self.delta = self._new_symb("_d%d", rf_type)
        params.append(self.delta)
        self.params = frozenset(params)

    @property
    def symbs(self) -> frozenset:
        return self.int_symbs | self.real_symbs

    @property
    def symbs_to_real(self) -> frozenset:
        return frozenset(self.env.formula_manager.ToReal(s)
                         for s in self.int_symbs) | self.real_symbs

    @property
    def symbs_to_same_type(self) -> frozenset:
        if self.real_symbs:
            return self.symbs_to_real
        return self.int_symbs

    def desc_template(self) -> str:
        return "PR ranking template"

    def subst(self, fm: FNode, model) -> FNode:
        assert isinstance(fm, FNode)
        assert fm in self.env.formula_manager.formulae.values()
        return self.env.substituter.substitute(fm, model)

    def simpl(self, fm: FNode) -> FNode:
        assert isinstance(fm, FNode)
        assert fm in self.env.formula_manager.formulae.values()
        return self.env.simplifier.simplify(fm)

    def progress_pred(self, model=None) -> FNode:
        """Return predicate which is true if curr-next pair is ranked"""
        mgr = self.env.formula_manager
        x_rf_expr = to_next(mgr, self.rf_expr, self.symbs)
        res = mgr.And(self.rf_pred,
                      mgr.LE(x_rf_expr, mgr.Minus(self.rf_expr, self.delta)))
        if model:
            res = self.simpl(self.subst(res, model))
        return res

    def ef_instantiate(self, extra=None):
        mgr = self.env.formula_manager
        generaliser = Generaliser(self.env, self.cn, self.totime)
        try:
            solver_it = iter(get_solvers())
            solver = next(solver_it)
            log("\tUsing solver {} for ranking-function EF-constraints"
                .format(solver),
                RankingFunction._LOG_LVL)
            constrs = list(self.constraints)

            if extra:
                constrs.extend(extra)

            constrs = mgr.And(constrs)
            symbs = constrs.get_free_variables() - self.params
            res, learn = efsolve(self.env, self.params, symbs,
                                 constrs, esolver_name=solver,
                                 fsolver_name=solver,
                                 generaliser=generaliser)
            constrs = mgr.And(constrs, mgr.And(learn))
            while res is None:
                solver = next(solver_it)
                log("\tUsing solver {} for ranking-function EF-constraints"
                    .format(solver),
                    RankingFunction._LOG_LVL)
                res, c_learn = efsolve(self.env, self.params, symbs,
                                       constrs,
                                       esolver_name=solver,
                                       fsolver_name=solver)
                constrs = mgr.And(constrs, mgr.And(c_learn))
                learn.extend(c_learn)
        except StopIteration:
            return None, learn
        return res, learn

    def motzkin_instantiate(self, extra=None):
        o_norm = self.env.formula_manager.normalize
        i_env = PysmtEnv()
        i_norm = i_env.formula_manager.normalize
        res = None
        solver_it = iter(get_solvers())
        extra = [i_norm(c) for c in extra] if extra else []
        approx = None
        if approximate():
            approx = RationalApprox()

        try:
            solver = next(solver_it)
            log("\tUsing solver {} for ranking-function motzkin-constraints"
                .format(solver),
                RankingFunction._LOG_LVL)

            with Solver(env=i_env, name=solver) as solver:
                for c in extra:
                    solver.add_assertion(c)
                for c in self.generate_motzkin_constr():
                    solver.add_assertion(i_norm(c))
                try:
                    res = solve_with_timeout(RankingFunction.get_timeout(),
                                             solver)
                except SolverReturnedUnknownResultError:
                    log("\t\tMotzkinRanker timeout", RankingFunction._LOG_LVL)
                    log("\n{}\n".format(to_smt2(solver.assertions)),
                        RankingFunction._LOG_LVL + 1)
                    res = None

                if res is True:
                    model = self.try_simpl_model(i_env, solver, approx)
                    return {o_norm(k): o_norm(v) for k, v in model.items()}
                if res is False:
                    return None
                constrs = solver.assertions

            assert res is None, res
            assert constrs is not None

            while res is None:
                solver = next(solver_it)
                log("\tUsing solver {} for motzkin constraints".format(solver),
                    RankingFunction._LOG_LVL)

                with Solver(env=i_env, name=solver) as solver:
                    for c in constrs:
                        assert c in i_env.formula_manager.formulae.values()
                        solver.add_assertion(c)
                    try:
                        res = solve_with_timeout(RankingFunction.get_timeout(),
                                                 solver)
                    except SolverReturnedUnknownResultError:
                        log("\t\tMotzkinRanker timeout",
                            RankingFunction._LOG_LVL)
                        log("\n{}\n".format(to_smt2(solver.assertions)),
                            RankingFunction._LOG_LVL + 1)
                        res = None

                    if res is True:
                        model = self.try_simpl_model(i_env, solver, approx)
                        return {o_norm(k): o_norm(v) for k, v in model.items()}
                    if res is False:
                        return None
        except StopIteration:
            return None
        assert False, "unreachable code"

    def try_simpl_model(self, env, solver, approx):
        mgr = env.formula_manager
        norm = mgr.normalize
        model = solver.get_values(norm(k) for k in self.params)
        if not approx:
            return model

        sat = False
        solver.push()
        for k, v in model.items():
            if v.is_bool_constant():
                eq = k if v.is_true() else mgr.Not(k)
            else:
                val = approx(v.constant_value())
                val = mgr.Real(val) if v.is_real_constant() \
                    else mgr.Int(int(val))
                eq = mgr.Equals(k, val)
            solver.add_assertion(eq)
        try:
            sat = solve_with_timeout(RankingFunction.get_timeout(),
                                     solver)
        except SolverReturnedUnknownResultError:
            sat = None

        if sat is True:
            model = solver.get_values(norm(k) for k in self.params)
        solver.pop()
        return model

    def generate_motzkin_constr(self):
        mgr = self.env.formula_manager
        for lhs, rhs in self.implications:
            assert isinstance(lhs, frozenset), lhs
            assert isinstance(rhs, frozenset), rhs
            assert len(lhs) + len(rhs) > 0
            assert all(isinstance(l, FNode) for l in lhs)
            assert all(not l.is_false() for l in lhs)
            assert all(isinstance(r, FNode) for r in rhs)
            if all(s.get_free_variables() <= self.params
                   for s in chain(lhs, rhs)):
                constr = self.simpl(mgr.Implies(mgr.And(lhs),
                                                mgr.And(rhs)))
                yield constr
            else:
                if all(not r.is_true() for r in rhs):
                    # lhs = [simpl(subst(l, debug_substs)) for l in lhs]
                    # rhs = [simpl(subst(r, debug_substs)) for r in rhs]
                    constrs = frozenset(filter(lambda x: not x.is_true(),
                                               chain(lhs,
                                                     (self.not_rel(r)
                                                      for r in rhs))))
                    yield from motzkin_transpose(self.env, constrs,
                                                 self.td, self.cn,
                                                 self.params)

    def split_eq(self, fm: FNode) -> list:
        assert isinstance(fm, FNode)
        mgr = self.env.formula_manager
        if fm.is_equals():
            ge = mgr.GE(fm.arg(0), fm.arg(1))
            le = mgr.LE(fm.arg(0), fm.arg(1))
            return [ge, le]
        assert fm.is_constant() or fm.is_le() or fm.is_lt(), fm.serialize()
        return [fm]

    def not_rel(self, rel: FNode) -> FNode:
        mgr = self.env.formula_manager
        assert rel in mgr.formulae.values()
        if rel.is_true():
            return mgr.FALSE()
        if rel.is_false():
            return mgr.TRUE()

        assert rel.is_le() or rel.is_lt(), "{}".format(rel.serialize())
        lhs = rel.arg(0)
        rhs = rel.arg(1)
        rv = rel
        if rel.is_le():
            rv = mgr.GT(lhs, rhs)
        elif rel.is_lt():
            rv = mgr.GE(lhs, rhs)
        if __debug__:
            with Solver(env=self.env) as _solver:
                n_rv = mgr.Not(rv)
                equals = mgr.Iff(rel, n_rv)
                n_equals = mgr.Not(equals)
                _solver.add_assertion(n_equals)
                if _solver.solve():
                    assert False, "{}: {}".format(equals, _solver.get_model())
        return rv

    @property
    def constraints(self):
        """Return iterable of Exist-Forall quantified constraints"""
        mgr = self.env.formula_manager
        for lhs, rhs in self._get_constr():
            assert isinstance(lhs, frozenset)
            assert isinstance(rhs, frozenset)
            assert all(isinstance(l, FNode) for l in lhs)
            assert all(isinstance(r, FNode) for r in rhs)
            yield self.simpl(mgr.Implies(mgr.And(lhs),
                                         mgr.Or(rhs)))

    @property
    def implications(self):
        """Return pairs of implications [lhs] -> [rhs]

        lhs is purely conjunctive and rhs is purely disjunctive.
        """
        yield from self._get_constr()

    def _get_constr(self) -> Generator[Tuple[frozenset, frozenset], None, None]:
        mgr = self.env.formula_manager
        lhs = frozenset([mgr.TRUE()])
        # delta > 0
        rhs = frozenset([mgr.GT(self.delta, self.rf_zero)])
        assert all(len(r.get_atoms()) == 1 for r in rhs)
        assert all(r.get_free_variables() <= self.params for r in rhs)
        assert all(isinstance(r, FNode) for r in rhs)
        yield lhs, rhs

        # states & trans -> rf' > 0
        lhs = [self.totime(s, idx)
               for idx, state in enumerate(self.states) for s in state]
        lhs.extend(self.totime(t, idx)
                   for idx, tr in enumerate(self.trans) for t in tr)
        lhs = frozenset(lhs)
        assert all(isinstance(l, FNode) for l in lhs)
        yield lhs, frozenset([self.totime(self.rf_pred, len(self.trans))])

        # states & trans -> rf' <= rf - delta
        rf0 = self.totime(self.rf_expr, 0)
        rf_last = self.totime(self.rf_expr, len(self.trans))
        rhs = mgr.LE(rf_last, mgr.Minus(rf0, self.delta))
        assert all(isinstance(l, FNode) for l in lhs)
        assert isinstance(rhs, FNode)
        yield lhs, frozenset([rhs])

    def _new_symb(self, base: str, s_type) -> FNode:
        """Return fresh symbol of the given type"""
        assert s_type in {types.BOOL, types.INT, types.REAL}
        if base is None:
            base = "%d"
        base = "{}{}".format(PREF, base)
        return self.env.formula_manager.new_fresh_symbol(s_type, base)

    def _linear_comb(self, symbs: Union[set, frozenset],
                     idx: int = None) -> Tuple[FNode, list]:
        """Return FNode expr representing linear combination of symbs and
        list of parameters"""
        assert isinstance(symbs, (set, frozenset))
        assert idx is None or isinstance(idx, int), idx
        assert all(self.env.stc.get_type(s).is_int_type() for s in symbs) or \
            all(self.env.stc.get_type(s).is_real_type() for s in symbs)
        mgr = self.env.formula_manager
        m_type = types.REAL
        if symbs and self.env.stc.get_type(next(iter(symbs))).is_int_type():
            m_type = types.INT

        k = self._new_symb("_k%d", m_type)
        res = [k]
        params = [k]
        for s in symbs:
            if idx is not None:
                s = self.totime(s, idx)
            coeff = self._new_symb("_c%d", m_type)
            params.append(coeff)
            res.append(mgr.Times(coeff, s))
        res = mgr.Plus(res)
        assert all(p in mgr.get_all_symbols() for p in params)
        return res, params

    def _debug_check(self, model) -> Tuple[bool, FNode]:
        mgr = self.env.formula_manager
        with Solver(env=self.env) as solver:
            for _c in self.constraints:
                c = self.simpl(self.subst(_c, model))
                solver.add_assertion(mgr.Not(c))
                if solver.solve() is not False:
                    return False, c
                solver.reset_assertions()

        return True, None
