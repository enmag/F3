from typing import Iterator, Tuple, FrozenSet, List, Optional, Dict, Union
from itertools import chain

from pysmt.environment import Environment as PysmtEnv
from pysmt.fnode import FNode
import pysmt.typing as types
from pysmt.exceptions import SolverReturnedUnknownResultError

from expr_at_time import ExprAtTime
from canonize import Canonizer
from generalise import Generaliser
from rationalapprox import RationalApprox
from efsolver import efsolve
from solver import get_solvers
from multisolver import MultiSolver
from motzkin import motzkin_transpose
from rewritings import TimesDistributor
from rankfun import RankFun
from utils import log, linear_comb, new_symb, default_key


class Ranker:
    PREF = "_rank"
    _TIMEOUT = 25
    _LOG_LVL = 1
    _APPROXIMATE = True

    @staticmethod
    def set_timeout(val: int) -> None:
        assert isinstance(val, int)
        Ranker._TIMEOUT = val

    @staticmethod
    def get_timeout() -> int:
        return Ranker._TIMEOUT

    @staticmethod
    def set_approximate(val: bool) -> None:
        assert isinstance(val, bool)
        Ranker._APPROXIMATE = val

    @staticmethod
    def get_approximate() -> bool:
        return Ranker._APPROXIMATE

    def __init__(self, env: PysmtEnv, td: TimesDistributor, cn: Canonizer):
        assert isinstance(env, PysmtEnv)
        assert isinstance(td, TimesDistributor)
        assert isinstance(cn, Canonizer)
        assert td.env == env
        assert cn.env == env

        self.env = env
        self.td = td
        self.cn = cn
        self.totime = ExprAtTime(env=env, ignore_pref=Ranker.PREF)

    def _linear_comb(self, symbs: FrozenSet[FNode],
                     idx: int = None) -> Tuple[FNode, List[FNode]]:
        return linear_comb(self.env, symbs, Ranker.PREF, idx=idx,
                           totime=self.totime)

    def subst(self, fm: FNode, model) -> FNode:
        assert isinstance(fm, FNode)
        assert fm in self.env.formula_manager.formulae.values()

        return self.env.substituter.substitute(fm, model)

    def simpl(self, fm: FNode) -> FNode:
        assert isinstance(fm, FNode)
        assert fm in self.env.formula_manager.formulae.values()

        return self.env.simplifier.simplify(fm)

    def split_eq(self, fm: FNode) -> List[FNode]:
        assert isinstance(fm, FNode)
        assert fm in self.env.formula_manager.formulae.values()

        mgr = self.env.formula_manager
        if fm.is_equals():
            ge = mgr.GE(fm.arg(0), fm.arg(1))
            le = mgr.LE(fm.arg(0), fm.arg(1))
            return [ge, le]
        assert fm.is_constant() or fm.is_le() or fm.is_lt()
        return [fm]

    def not_rel(self, rel: FNode) -> FNode:
        assert isinstance(rel, FNode)
        assert rel in self.env.formula_manager.formulae.values()

        mgr = self.env.formula_manager
        if rel.is_true():
            return mgr.FALSE()
        if rel.is_false():
            return mgr.TRUE()

        assert rel.is_le() or rel.is_lt()
        lhs = rel.arg(0)
        rhs = rel.arg(1)
        rv = rel
        if rel.is_le():
            rv = mgr.GT(lhs, rhs)
        elif rel.is_lt():
            rv = mgr.GE(lhs, rhs)
        if __debug__:
            from solver import Solver
            with Solver(env=self.env) as _solver:
                n_rv = mgr.Not(rv)
                equals = mgr.Iff(rel, n_rv)
                n_equals = mgr.Not(equals)
                _solver.add_assertion(n_equals)
                assert _solver.solve() is False
        return rv

    def rank_templates(self, symbs: FrozenSet[FNode]) -> Iterator[RankFun]:
        assert isinstance(symbs, frozenset)
        assert all(isinstance(s, FNode) for s in symbs)
        assert all(s in self.env.formula_manager.get_all_symbols()
                   for s in symbs)
        assert all(self.env.stc.walk(s).is_int_type() or
                   self.env.stc.walk(s).is_real_type()
                   for s in symbs)
        expr_type = types.INT
        stc = self.env.stc.walk
        mgr = self.env.formula_manager
        if any(stc(s).is_real_type() for s in symbs):
            expr_type = types.REAL
            symbs = frozenset(s if stc(s).is_real_type()
                              else mgr.ToReal(s)
                              for s in symbs)
        expr, params = self._linear_comb(symbs)
        delta = new_symb(mgr, f"{Ranker.PREF}_delta", expr_type)
        params.append(delta)
        yield RankFun(self.env, expr, delta, symbs, frozenset(params))

    def ef_instantiate(self, rf: RankFun,
                       states: List[FrozenSet[FNode]],
                       trans: List[FrozenSet[FNode]],
                       extra: Optional[List[FNode]] = None) \
                    -> Tuple[Union[Dict[FNode, FNode], Optional[bool]],
                             List[FNode]]:
        assert isinstance(rf, RankFun)
        assert isinstance(states, list)
        assert all(isinstance(s, (frozenset, set)) for s in states)
        assert all(isinstance(pred, FNode) for s in states for pred in s)
        assert all(pred in self.env.formula_manager.formulae.values()
                   for s in states for pred in s)
        assert isinstance(trans, list)
        assert all(isinstance(t, (frozenset, set)) for t in trans)
        assert all(isinstance(pred, FNode) for t in trans for pred in t)
        assert all(pred in self.env.formula_manager.formulae.values()
                   for t in trans for pred in t)
        assert extra is None or isinstance(extra, list)
        assert extra is None or all(isinstance(e, FNode) for e in extra)
        assert extra is None or \
            all(e in self.env.formula_manager.formulae.values()
                for e in extra)

        mgr = self.env.formula_manager
        generalise = Generaliser(self.env, self.cn, self.totime)

        try:
            solver_it = iter(get_solvers())
            solver = next(solver_it)
            log("\tUsing solver {} for ranking-function EF-constraints"
                .format(solver), Ranker._LOG_LVL)
            constrs = list(self.constraints(rf, states, trans))

            if extra:
                constrs.extend(extra)

            constrs = mgr.And(constrs)
            symbs = self.env.fvo.walk(constrs) - rf.params
            res, learn = efsolve(self.env, rf.params, symbs,
                                 constrs, esolver_name=solver,
                                 fsolver_name=solver,
                                 generalise=generalise)
            constrs = mgr.And(constrs, mgr.And(learn))
            while res is None:
                solver = next(solver_it)
                log("\tUsing solver {} for ranking-function EF-constraints"
                    .format(solver), Ranker._LOG_LVL)
                res, c_learn = efsolve(self.env, rf.params, symbs,
                                       constrs,
                                       esolver_name=solver,
                                       fsolver_name=solver)
                constrs = mgr.And(constrs, mgr.And(c_learn))
                learn.extend(c_learn)
        except StopIteration:
            return None, learn
        return res, learn

    def motzkin_instantiate(self, rf: RankFun, states: List[FrozenSet[FNode]],
                            trans: List[FrozenSet[FNode]],
                            extra: Optional[List[FNode]] = None) \
                        -> Union[Dict[FNode, FNode], Optional[bool]]:
        assert isinstance(rf, RankFun)
        assert rf.env == self.env
        assert isinstance(states, list)
        assert all(isinstance(s, (frozenset, set)) for s in states)
        assert all(isinstance(pred, FNode) for s in states for pred in s)
        assert all(pred in self.env.formula_manager.formulae.values()
                   for s in states for pred in s)
        assert isinstance(trans, list)
        assert all(isinstance(t, (frozenset, set)) for t in trans)
        assert all(isinstance(pred, FNode) for t in trans for pred in t)
        assert all(pred in self.env.formula_manager.formulae.values()
                   for t in trans for pred in t)
        assert extra is None or isinstance(extra, list)
        assert extra is None or all(isinstance(e, FNode) for e in extra)
        assert extra is None or \
            all(e in self.env.formula_manager.formulae.values()
                for e in extra)

        o_norm = self.env.formula_manager.normalize
        i_env = PysmtEnv()
        i_norm = i_env.formula_manager.normalize
        approx = RationalApprox() if Ranker.get_approximate() else None
        res = None
        log("\tUsing motzkin-constraints", Ranker._LOG_LVL)
        with MultiSolver(i_env, Ranker.get_timeout(),
                         log_lvl=Ranker._LOG_LVL) as solver:
            if extra:
                for c in extra:
                    solver.add_assertion(i_norm(c))
            for c in self.generate_motzkin_constr(rf, states, trans):
                solver.add_assertion(i_norm(c))
            try:
                res = solver.solve()
            except SolverReturnedUnknownResultError:
                log("\t\tMotzkinRanker timeout", Ranker._LOG_LVL)
                # log(f"\n{to_smt2(i_env, solver.assertions)}\n", Ranker._LOG_LVL + 1)
                res = None

            if res is True:
                assert rf.env == self.env
                # solver is unusable after this call.
                model = Ranker.simpl_model(i_env, solver,
                                           i_norm(rf.delta),
                                           frozenset(i_norm(p)
                                                     for p in rf.params),
                                           approx)
                return {o_norm(k): o_norm(v) for k, v in model.items()}
        return res

    @staticmethod
    def simpl_model(env: PysmtEnv, solver, delta: FNode,
                    params: FrozenSet[FNode],
                    approx: Optional[RationalApprox]) -> Dict[FNode, FNode]:
        assert isinstance(env, PysmtEnv)
        assert isinstance(delta, FNode)
        assert isinstance(params, frozenset)
        assert all(isinstance(p, FNode) for p in params)
        assert delta in params
        assert all(p in env.formula_manager.get_all_symbols() for p in params)
        assert all(p.symbol_type().is_int_type() or
                   p.symbol_type().is_real_type()
                   for p in params)
        assert approx is None or isinstance(approx, RationalApprox)
        model = solver.get_values(params)
        d_val = model[delta]
        if d_val.is_constant(_type=types.REAL):
            # remove denominator from d_val
            assert hasattr(d_val.constant_value(), "numerator")
            assert hasattr(d_val.constant_value(), "denominator")
            assert d_val.constant_value().denominator > 0
            mgr = env.formula_manager
            simpl = env.simplifier.simplify
            den = mgr.Real(d_val.constant_value().denominator)
            model = {p: simpl(mgr.Times(model[p], den))
                     for p in params}
            assert model[delta].constant_value() == d_val.constant_value().numerator

        if not approx:
            return model

        mgr = env.formula_manager
        for k, v in model.items():
            val = approx(v.constant_value())
            val = mgr.Real(val) if v.is_real_constant() \
                else mgr.Int(int(val))
            eq = mgr.Equals(k, val)
            solver.add_assertion(eq)
        try:
            if solver.solve() is True:
                return solver.get_values(params)
        except SolverReturnedUnknownResultError:
            pass
        log("\tRankFun model simplification failed", Ranker._LOG_LVL)
        return model

    def generate_motzkin_constr(self, rf: RankFun,
                                states: List[FrozenSet[FNode]],
                                trans: List[FrozenSet[FNode]]) -> Iterator[FNode]:
        assert isinstance(rf, RankFun)
        assert rf.env == self.env
        assert isinstance(states, list)
        assert all(isinstance(s, (frozenset, set)) for s in states)
        assert all(isinstance(pred, FNode) for s in states for pred in s)
        assert all(pred in self.env.formula_manager.formulae.values()
                   for s in states for pred in s)
        assert isinstance(trans, list)
        assert all(isinstance(t, (frozenset, set)) for t in trans)
        assert all(isinstance(pred, FNode) for t in trans for pred in t)
        assert all(pred in self.env.formula_manager.formulae.values()
                   for t in trans for pred in t)

        mgr = self.env.formula_manager
        get_free_vars = self.env.fvo.walk
        for lhs, rhs in self.implications(rf, states, trans):
            assert isinstance(lhs, frozenset), lhs
            assert isinstance(rhs, frozenset), rhs
            assert len(lhs) + len(rhs) > 0
            assert all(isinstance(l, FNode) for l in lhs)
            assert all(not l.is_false() for l in lhs)
            assert all(isinstance(r, FNode) for r in rhs)
            if all(get_free_vars(s) <= rf.params
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
                                                 self.td, rf.params)

    def constraints(self, rf: RankFun,
                    states: List[FrozenSet[FNode]],
                    trans: List[FrozenSet[FNode]]) -> Iterator[FNode]:
        """Return iterable of Exist-Forall quantified constraints"""
        assert isinstance(rf, RankFun)
        assert isinstance(states, list)
        assert all(isinstance(s, (frozenset, set)) for s in states)
        assert all(isinstance(pred, FNode) for s in states for pred in s)
        assert all(pred in self.env.formula_manager.formulae.values()
                   for s in states for pred in s)
        assert isinstance(trans, list)
        assert all(isinstance(t, (frozenset, set)) for t in trans)
        assert all(isinstance(pred, FNode) for t in trans for pred in t)
        assert all(pred in self.env.formula_manager.formulae.values()
                   for t in trans for pred in t)

        mgr = self.env.formula_manager
        for lhs, rhs in self._get_constr(rf, states, trans):
            assert isinstance(lhs, frozenset)
            assert isinstance(rhs, frozenset)
            assert all(isinstance(l, FNode) for l in lhs)
            assert all(isinstance(r, FNode) for r in rhs)
            yield self.simpl(mgr.Implies(mgr.And(lhs),
                                         mgr.Or(rhs)))

    def implications(self, rf: RankFun,
                     states: List[FrozenSet[FNode]],
                     trans: List[FrozenSet[FNode]]) \
                -> Iterator[Tuple[FrozenSet[FNode], FrozenSet[FNode]]]:
        """Return pairs of implications [lhs] -> [rhs]

        lhs is purely conjunctive and rhs is purely disjunctive.
        """
        assert isinstance(rf, RankFun)
        assert rf.env == self.env
        assert isinstance(states, list)
        assert all(isinstance(s, (frozenset, set)) for s in states)
        assert all(isinstance(pred, FNode) for s in states for pred in s)
        assert all(pred in self.env.formula_manager.formulae.values()
                   for s in states for pred in s)
        assert isinstance(trans, list)
        assert all(isinstance(t, (frozenset, set)) for t in trans)
        assert all(isinstance(pred, FNode) for t in trans for pred in t)
        assert all(pred in self.env.formula_manager.formulae.values()
                   for t in trans for pred in t)

        yield from self._get_constr(rf, states, trans)

    def _get_constr(self, rf: RankFun, states: List[FrozenSet[FNode]],
                    trans: List[FrozenSet[FNode]]) \
                -> Iterator[Tuple[FrozenSet[FNode], FrozenSet[FNode]]]:
        assert isinstance(rf, RankFun)
        assert rf.env == self.env
        assert isinstance(states, list)
        assert isinstance(trans, list)
        assert all(isinstance(c, (set, frozenset)) for c in states)
        assert all(isinstance(c, (set, frozenset)) for c in trans)
        assert all(isinstance(c, FNode) for s in states for c in s)
        assert all(isinstance(c, FNode) for s in trans for c in s)
        assert all(c in self.env.formula_manager.formulae.values()
                   for s in states for c in s)
        assert all(c in self.env.formula_manager.formulae.values()
                   for s in trans for c in s)
        assert len(states) == len(trans) + 1

        mgr = self.env.formula_manager
        lhs = frozenset([mgr.TRUE()])
        # delta > 0
        delta = rf.delta
        rf_expr = rf.expr
        rhs = frozenset([mgr.GT(delta, rf.min_el)])
        assert all(len(self.env.ao.get_atoms(r)) == 1 for r in rhs)
        assert all(self.env.fvo.walk(r) <= rf.params for r in rhs)
        assert all(isinstance(r, FNode) for r in rhs)
        yield lhs, rhs

        # states & trans -> rf' > 0
        lhs = [self.totime(s, idx)
               for idx, state in enumerate(states) for s in state]
        lhs.extend(self.totime(t, idx)
                   for idx, tr in enumerate(trans) for t in tr)
        lhs = frozenset(lhs)
        assert all(isinstance(l, FNode) for l in lhs)
        yield lhs, frozenset([self.totime(self.cn(mgr.GT(rf_expr, rf.min_el)),
                                          len(trans))])

        # states & trans -> rf' <= rf - delta
        rf0 = self.totime(rf_expr, 0)
        rf_last = self.totime(rf_expr, len(trans))
        rhs = mgr.LE(rf_last, mgr.Minus(rf0, delta))
        assert all(isinstance(l, FNode) for l in lhs)
        assert isinstance(rhs, FNode)
        yield lhs, frozenset([rhs])

    def _debug_check(self, model, rf: RankFun,
                     states: List[FrozenSet[FNode]],
                     trans: List[FrozenSet[FNode]]) -> Tuple[bool, FNode]:
        assert isinstance(rf, RankFun)
        assert rf.env == self.env
        assert isinstance(states, list)
        assert isinstance(trans, list)
        assert all(isinstance(c, (set, frozenset)) for c in states)
        assert all(isinstance(c, (set, frozenset)) for c in trans)
        assert all(isinstance(c, FNode) for s in states for c in s)
        assert all(isinstance(c, FNode) for s in trans for c in s)
        assert all(c in self.env.formula_manager.formulae.values()
                   for s in states for c in s)
        assert all(c in self.env.formula_manager.formulae.values()
                   for s in trans for c in s)
        assert len(states) == len(trans) + 1

        mgr = self.env.formula_manager
        with MultiSolver(self.env, Ranker.get_timeout()) as solver:
            for _c in self.constraints(rf, states, trans):
                c = self.simpl(self.subst(_c, model))
                solver.add_assertion(mgr.Not(c))
                if solver.solve() is not False:
                    return False, c
                solver.reset_assertions()
        return True, None
