from __future__ import annotations
from typing import (FrozenSet, Set, List, Tuple, Dict, Iterable, Iterator,
                    Union, Optional)
from itertools import chain
from io import StringIO
from collections import defaultdict

from pysmt.environment import Environment as PysmtEnv
from pysmt.fnode import FNode
from pysmt.exceptions import SolverReturnedUnknownResultError
from pysmt.typing import REAL as PyReal
from pysmt.rewritings import NNFizer

from canonize import Canonizer
from expr_at_time import ExprAtTime
from rankfun import RankFun, IRankFun, RRankFun
from ineq import eq2assign
from implicant import Implicant
from multisolver import MultiSolver
from efsolver import efmultisolve
from motzkin import motzkin_solve
from expr_utils import (symb_is_curr, to_curr, get_times, not_rels, not_rel,
                        symb2next, symb_is_next, to_next, is_atom,
                        assign2fnode, assigns2fnodes, linear_comb, new_param)


class Funnel:
    """Funnel without internal loops: fixed number of steps"""
    _PROP_TIMEOUT = 10
    _USE_EF = True
    _USE_MOTZKIN = True
    _CONST_SYMBS_TIMEOUT = 5
    _LOG_LVL = 2

    @staticmethod
    def set_log_lvl(val: int) -> None:
        assert isinstance(val, int)
        Funnel._LOG_LVL = val

    @staticmethod
    def get_log_lvl() -> int:
        return Funnel._LOG_LVL

    @staticmethod
    def set_propagate_timeout(val: int) -> None:
        assert isinstance(val, int)
        assert val > 0
        Funnel._PROP_TIMEOUT = val

    @staticmethod
    def get_propagate_timeout() -> int:
        return Funnel._PROP_TIMEOUT

    @staticmethod
    def set_use_ef(val: bool) -> None:
        assert isinstance(val, bool)
        Funnel._USE_EF = val

    @staticmethod
    def get_use_ef() -> bool:
        return Funnel._USE_EF

    @staticmethod
    def set_use_motzkin(val: bool) -> None:
        assert isinstance(val, bool)
        Funnel._USE_MOTZKIN = val

    @staticmethod
    def get_use_motzkin() -> bool:
        return Funnel._USE_MOTZKIN

    @staticmethod
    def set_const_symbs_timeout(val: int) -> None:
        assert isinstance(val, int)
        assert val >= 0
        Funnel._CONST_SYMBS_TIMEOUT = val

    @staticmethod
    def get_const_symbs_timeout() -> int:
        return Funnel._CONST_SYMBS_TIMEOUT

    def __init__(self, env: PysmtEnv, first_idx: int,
                 symbs: FrozenSet[FNode],
                 states: List[Dict[FNode, FNode]],
                 assigns: List[Dict[FNode, FNode]],
                 regions: List[Set[FNode]],
                 t_eqs: List[Dict[FNode, FNode]],
                 trans: List[Set[FNode]],
                 h_regions: List[Set[FNode]],
                 h_trans: List[Set[FNode]],
                 totime: ExprAtTime, cn: Canonizer):
        assert isinstance(env, PysmtEnv)
        assert isinstance(first_idx, int)
        assert first_idx >= 0
        assert isinstance(symbs, frozenset)
        assert all(isinstance(s, FNode) for s in symbs)
        assert all(s.is_symbol() for s in symbs)
        assert all(symb_is_curr(s) for s in symbs)
        assert all(s in env.formula_manager.get_all_symbols() for s in symbs)
        assert isinstance(states, list)
        assert len(states) > 0
        assert all(isinstance(state, dict) for state in states)
        assert all(isinstance(s, FNode) for state in states for s in state)
        assert all(isinstance(v, FNode) for state in states
                   for v in state.values())
        assert all(s in env.formula_manager.get_all_symbols()
                   for state in states for s in state)
        assert all(v.is_constant() for state in states for v in state.values())
        assert all(v in env.formula_manager.formulae.values()
                   for state in states for v in state.values())
        assert all(symbs <= state.keys() for state in states)
        assert all(len(symbs & assign.keys()) == 0 for assign in assigns)
        assert isinstance(assigns, list)
        assert len(assigns) == len(states)
        assert all(isinstance(state, dict) for state in assigns)
        assert all(isinstance(s, FNode) for state in assigns for s in state)
        assert all(s in env.formula_manager.get_all_symbols()
                   for state in assigns for s in state)
        assert all(symb_is_curr(s) for state in assigns for s in state)
        assert all(isinstance(v, FNode)
                   for state in assigns for v in state.values())
        assert all(v in env.formula_manager.formulae.values()
                   for state in assigns for v in state.values())
        assert all(v.is_constant()
                   for state in assigns for v in state.values())
        assert all(frozenset(state.keys()) == frozenset(assigns[0].keys())
                   for state in assigns[1:])
        assert isinstance(regions, list)
        assert len(regions) == len(assigns)
        assert all(isinstance(reg, (set, frozenset, list)) for reg in regions)
        assert all(isinstance(p, FNode) for reg in regions for p in reg)
        assert all(p in env.formula_manager.formulae.values()
                   for reg in regions for p in reg)
        assert all(env.fvo.get_free_variables(p) <= symbs
                   for reg in regions for p in reg)
        assert isinstance(t_eqs, list)
        assert all(isinstance(eq, dict) for eq in t_eqs)
        assert all(isinstance(k, FNode) for eq in t_eqs for k in eq)
        assert all(k in env.formula_manager.get_all_symbols()
                   for eq in t_eqs for k in eq)
        assert all(k.is_symbol() for eq in t_eqs for k in eq)
        assert all(symb_is_next(k) for eq in t_eqs for k in eq)
        assert all(isinstance(v, FNode) for eq in t_eqs for v in eq.values())
        assert all(v in env.formula_manager.formulae.values()
                   for eq in t_eqs for v in eq.values())
        assert isinstance(trans, list)
        assert len(trans) == len(regions)
        assert all(isinstance(t, (set, frozenset, list)) for t in trans)
        assert all(isinstance(p, FNode) for t in trans for p in t)
        assert all(p in env.formula_manager.formulae.values()
                   for t in trans for p in t)
        assert all(env.fvo.get_free_variables(p) <= symbs |
                   frozenset(symb2next(env, s) for s in symbs)
                   for t in trans for p in t)
        assert isinstance(h_regions, list)
        assert len(h_regions) == len(regions)
        assert all(isinstance(reg, (set, frozenset, list))
                   for reg in h_regions)
        assert all(isinstance(p, FNode) for reg in h_regions for p in reg)
        assert all(p in env.formula_manager.formulae.values()
                   for reg in h_regions for p in reg)
        assert all(env.fvo.get_free_variables(p) <= symbs
                   for reg in h_regions for p in reg)
        assert isinstance(h_trans, list)
        assert len(h_trans) == len(regions)
        assert all(isinstance(t, (set, frozenset, list)) for t in h_trans)
        assert all(isinstance(p, FNode) for t in h_trans for p in t)
        assert all(p in env.formula_manager.formulae.values()
                   for t in h_trans for p in t)
        assert all(env.fvo.get_free_variables(p) <= symbs |
                   frozenset(symb2next(env, s) for s in symbs)
                   for t in h_trans for p in t)
        assert isinstance(totime, ExprAtTime)
        assert totime.env == env
        assert isinstance(cn, Canonizer)
        assert cn.env == env

        self.env = env
        self.first_idx = first_idx
        self.symbs = symbs
        self.x_symbs = frozenset(symb2next(self.env, s) for s in self.symbs)
        self.cn = cn
        self.totime = totime
        self.params: Set[FNode] = set()
        self.int_symbs = frozenset(s for s in self.symbs
                                   if s.symbol_type().is_int_type())
        self.real_symbs = self.symbs - self.int_symbs
        assert all(s.symbol_type().is_real_type() for s in self.real_symbs)
        if not self.real_symbs:
            self.same_type_symbs = self.int_symbs
        else:
            mgr = self.env.formula_manager
            self.same_type_symbs = self.real_symbs | \
                frozenset(mgr.ToReal(s) for s in self.int_symbs)

        # make copy to avoid side-effects.
        self.states = [dict(state) for state in states]
        self.assigns = [dict(state) for state in assigns]
        self.regs = [set(r) for r in regions]
        self.t_eqs = [dict(eq) for eq in t_eqs]
        self.trans = [set(t) for t in trans]
        self.h_regs = [set(r) for r in h_regions]
        self.h_trans = [set(t) for t in h_trans]
        self.u_eqs: List[Dict[FNode, FNode]] = [{} for _ in t_eqs]
        self.u_reg: Set[FNode] = set()
        # set of predicates that hold at region 0 because of previous steps.
        self.impl_reg: FrozenSet[FNode] = frozenset()
        self.h_impl_reg: FrozenSet[FNode] = frozenset()

        assert all(self.env.fvo.get_free_variables(p) <= self.symbs
                   for reg in self.regs for p in reg)
        assert all(self.env.fvo.get_free_variables(p) <= self.symbs
                   for reg in self.h_regs for p in reg)
        assert all(self.env.fvo.get_free_variables(p) <=
                   self.symbs | self.x_symbs
                   for tr in self.trans for p in tr)
        assert all(self.env.fvo.get_free_variables(p) <=
                   self.symbs | self.x_symbs
                   for tr in self.h_trans for p in tr)
        assert all(x_s in self.x_symbs
                   for eq in self.t_eqs for x_s in eq)

    def instantiate(self, model: Dict[FNode, FNode]) -> None:
        """Replace all parameters according to `model`"""
        assert self.params <= frozenset(model.keys())
        simpl = self.env.simplifier.simplify
        subst = self.env.substituter.substitute
        self.regs[0].update(simpl(subst(p, model)) for p in self.u_reg)
        self.u_reg = set()
        for t_eq, u_eq in zip(self.t_eqs, self.u_eqs):
            assert all(k not in t_eq for k in u_eq)
            t_eq.update((k, simpl(subst(v, model))) for k, v in u_eq.items())
            u_eq.clear()
        assert len(self.u_reg) == 0
        assert all(len(u_eq) == 0 for u_eq in self.u_eqs)
        assert all(len(self.env.fvo.get_free_variables(p) & self.params) == 0
                   for reg in self.regs for p in reg)
        assert all(len(self.env.fvo.get_free_variables(p) & self.params) == 0
                   for eq in self.t_eqs for p in eq.values())
        assert all(len(self.env.fvo.get_free_variables(p) & self.params) == 0
                   for h_reg in self.h_regs for p in h_reg)
        assert all(len(self.env.fvo.get_free_variables(p) & self.params) == 0
                   for h_tr in self.h_trans for p in h_tr)

    def mk_symbs_constant(self, symbs: FrozenSet[FNode],
                          last_state: Dict[FNode, FNode]) -> None:
        assert isinstance(symbs, (set, frozenset))
        assert len(symbs) > 0
        assert all(isinstance(s, FNode) for s in symbs)
        assert all(s in self.env.formula_manager.get_all_symbols()
                   for s in symbs)
        assert isinstance(last_state, dict)
        assert symbs <= last_state.keys()
        assert symbs <= self.symbs
        x_symbs = frozenset(symb2next(self.env, s) for s in symbs)
        self.symbs = self.symbs - symbs
        self.x_symbs = self.x_symbs - x_symbs
        assert self.x_symbs == frozenset(symb2next(self.env, s)
                                         for s in self.symbs)
        self.int_symbs = self.int_symbs & self.symbs
        self.real_symbs = self.real_symbs & self.symbs
        if not self.real_symbs:
            self.same_type_symbs = self.int_symbs
        else:
            mgr = self.env.formula_manager
            self.same_type_symbs = self.real_symbs | \
                frozenset(mgr.ToReal(s) for s in self.int_symbs)
        subst = self.env.substituter.substitute
        simpl = self.env.simplifier.simplify
        get_free_vars = self.env.fvo.get_free_variables
        mgr = self.env.formula_manager
        true = mgr.TRUE()
        for state, x_state, assign, reg, h_reg, eq, tr, h_tr in \
            zip(self.states, chain(self.states[1:], [last_state]),
                self.assigns, self.regs, self.h_regs,
                self.t_eqs, self.trans, self.h_trans):
            conc_assign = {s: state[s] for s in symbs}
            assign.update(conc_assign)
            conc_assign.update({symb2next(self.env, s): x_state[s]
                                for s in symbs})
            # reg.
            preds = set(self.cn(simpl(subst(p, conc_assign))) for p in reg)
            preds.discard(true)
            assert all(get_free_vars(p) <= self.symbs for p in preds)
            reg.clear()
            reg.update(preds)
            # h_reg.
            preds = set(self.cn(simpl(subst(p, conc_assign))) for p in h_reg)
            preds.discard(true)
            assert all(get_free_vars(p) <= self.symbs for p in preds)
            h_reg.clear()
            h_reg.update(preds)
            # tr.
            preds = set(self.cn(simpl(subst(p, conc_assign))) for p in tr)
            preds.discard(true)
            tr.clear()
            for p in preds:
                assert get_free_vars(p) <= (self.symbs | self.x_symbs)
                if get_free_vars(p) <= self.symbs:
                    reg.add(p)
                else:
                    tr.add(p)
            # h_tr.
            preds = set(self.cn(simpl(subst(p, conc_assign))) for p in h_tr)
            preds.discard(true)
            h_tr.clear()
            for p in preds:
                assert get_free_vars(p) <= (self.symbs | self.x_symbs)
                if get_free_vars(p) <= self.symbs:
                    h_reg.add(p)
                else:
                    h_tr.add(p)
            # eq.
            preds = set(cn(simpl(subst(mgr.Equals(s, eq[s]), conc_assign)))
                        for s in (x_symbs & eq.keys()))
            preds.discard(true)
            eq.clear()
            for p in preds:
                assert get_free_vars(p) <= (self.symbs | self.x_symbs)
                if get_free_vars(p) <= self.symbs:
                    reg.add(p)
                else:
                    tr.add(p)

    def filter_constant_symbs(self, lasso_symbs: FrozenSet[FNode],
                              last_state: Dict[FNode, FNode],
                              last_reg: Set[FNode],
                              last_h_reg: Set[FNode]) -> FrozenSet[FNode]:
        if len(lasso_symbs) == 0:
            return lasso_symbs
        mgr = self.env.formula_manager
        assertions = [self.totime(p, idx)
                      for idx, (reg, h_reg, eq, tr, h_tr) in
                      enumerate(zip(self.regs, self.h_regs, self.t_eqs,
                                    self.trans, self.h_trans))
                      for p in chain(reg, h_reg, tr, h_tr,
                                     assigns2fnodes(self.env, eq))]
        assertions.extend(self.totime(p, len(self.regs))
                          for p in chain(last_reg, last_h_reg))
        res = []
        states = list(self.states)
        states.append(last_state)
        with MultiSolver(self.env, Funnel.get_const_symbs_timeout(),
                         log_lvl=Funnel.get_log_lvl(),
                         solver_names=["msat"]) as solver:
            solver.add_assertions(assertions)
            solver.push()
            for s in lasso_symbs:
                # unsat (states & trans & s_0 = v_0 & !(/\ s_i = v_i))
                solver.add_assertion(mgr.Equals(self.totime(s, 0),
                                                states[0][s]))
                solver.add_assertion(mgr.Not(mgr.And(
                    mgr.Equals(self.totime(s, idx + 1), x_step[s])
                    for idx, x_step in enumerate(states[1:]))))
                try:
                    sat = solver.solve()
                except SolverReturnedUnknownResultError:
                    sat = None
                    solver.reset_assertions()
                    solver.add_assertions(assertions)
                    solver.push()
                solver.pop()
                if sat is False:
                    res.append(s)
                    for idx, step in enumerate(states):
                        eq = mgr.Equals(self.totime(s, idx), step[s])
                        solver.add_assertion(eq)
                        assertions.append(eq)
                solver.push()
        if __debug__:
            from solver import Solver
            # check validity of constant symbs.
            with Solver(env=self.env) as _solver:
                # abst_states & hint_states
                for c_time, (reg, h_reg) in enumerate(zip(self.regs, self.h_regs)):
                    for pred in chain(reg, h_reg):
                        assert isinstance(pred, FNode)
                        _solver.add_assertion(self.totime(pred, c_time))
                for c_time, (tr, h_tr) in enumerate(zip(self.trans, self.h_trans)):
                    for pred in chain(tr, h_tr):
                        _solver.add_assertion(self.totime(pred, c_time))
                for c_time, eq in enumerate(self.t_eqs):
                    for pred in assigns2fnodes(self.env, eq):
                        _solver.add_assertion(self.totime(pred, c_time))
                for s in res:
                    _solver.add_assertion(assign2fnode(self.env,
                                                       self.totime(s, 0),
                                                       states[0][s]))
                disj = []
                for idx, x_step in enumerate(self.states[1:]):
                    for s in res:
                        eq = assign2fnode(self.env, self.totime(s, idx + 1),
                                          x_step[s])
                        disj.append(eq)
                _solver.add_assertion(mgr.Not(mgr.And(disj)))
                assert _solver.solve() is False

        return frozenset(res)

    def first(self) -> Iterable[FNode]:
        return chain(self.regs[0], self.u_reg)

    def h_first(self) -> Iterable[FNode]:
        return self.h_regs[0]

    def write_hr(self, idx: int, buf: StringIO) -> int:
        assert isinstance(buf, StringIO)
        assert isinstance(idx, int)
        serialize = self.env.serializer.serialize
        simpl = self.env.simplifier.simplify
        for idx, (state, reg, eqs, u_eqs, tr, h_reg, h_tr) in enumerate(
                zip(self.assigns, self.regs, self.t_eqs, self.u_eqs,
                    self.trans, self.h_regs, self.h_trans),
                start=idx):
            buf.write(f"\tRegion: {idx}\n")
            for s in sorted(state.keys(), key=lambda s: s.symbol_name()):
                buf.write(f"\t\t{serialize(s)} := {serialize(state[s])}\n")
            if idx == 0:
                for p in self.u_reg:
                    buf.write(f"\t\t{serialize(simpl(p))}\n")
            for p in reg:
                buf.write(f"\t\t{serialize(simpl(p))}\n")
            for p in h_reg:
                buf.write(f"\t\t{serialize(simpl(p))}  (hint)\n")
            buf.write(f"\tTrans: {idx} -- {idx + 1}\n")
            for s in sorted(u_eqs, key=lambda s: s.symbol_name()):
                buf.write(f"\t\t{serialize(s)} := {serialize(simpl(u_eqs[s]))}\n")
            for s in sorted(eqs, key=lambda s: s.symbol_name()):
                buf.write(f"\t\t{serialize(s)} := {serialize(simpl(eqs[s]))}\n")
            for p in tr:
                buf.write(f"\t\t{serialize(simpl(p))}\n")
            for p in h_tr:
                buf.write(f"\t\t{serialize(simpl(p))}\t(hint)\n")
        return idx + 1

    def __len__(self) -> int:
        """Return number of regions in current funnel"""
        assert len(self.assigns) == len(self.regs)
        assert len(self.regs) == len(self.trans)
        assert len(self.regs) == len(self.t_eqs)
        assert len(self.regs) == len(self.h_regs)
        assert len(self.regs) == len(self.h_trans)
        return len(self.regs)

    def uapprox_regs(self, num_ineqs: int) -> None:
        assert isinstance(num_ineqs, int)
        assert num_ineqs >= 0
        mgr = self.env.formula_manager
        for _ in range(num_ineqs):
            ineq, params = linear_comb(self.env, self.same_type_symbs)
            self.params.update(params)
            zero = mgr.Real(0) if self.real_symbs else mgr.Int(0)
            self.u_reg.add(mgr.GE(ineq, zero))

    def uapprox_trans(self,
                      x_symbs: Union[Set[FNode], FrozenSet[FNode]]) -> None:
        assert isinstance(x_symbs, (set, frozenset))
        assert all(symb_is_curr(s) for s in self.symbs)
        assert all(isinstance(s, FNode) for s in x_symbs)
        assert all(s in self.env.formula_manager.get_all_symbols()
                   for s in x_symbs)
        assert all(symb_is_next(s) for s in x_symbs)
        for u_eq, t_eq in zip(self.u_eqs, self.t_eqs):
            for s in x_symbs - t_eq.keys():
                if s.symbol_type().is_int_type():
                    expr, params = linear_comb(self.env, self.int_symbs)
                else:
                    expr, params = linear_comb(self.env, self.same_type_symbs)
                self.params.update(params)
                u_eq[s] = expr

    def learn_eqs(self, preds: Iterable[FNode],
                  eqs: Dict[FNode, FNode],
                  impl: Implicant) -> Tuple[Union[Dict[FNode, Set[FNode]],
                                                  Set[FNode]],
                                            Set[FNode], Set[FNode]]:
        """Add in eqs the next assignments extracted from preds,
        return tuple partitioning the remaining preds in:
        current only, curr-next and next-only.
        Equalities are exploited to backward propagate predicates."""
        if __debug__:
            from itertools import tee
            preds, _preds = tee(preds, 2)
            _orig = list(_preds)
            assert all(impl.cn(p) == p for p in _preds)
            _orig.extend(assigns2fnodes(self.env, eqs))

        # learn all eq assignments in trans and h_trans
        simpl = self.env.simplifier.simplify
        subst = self.env.substituter.substitute
        get_free_vars = self.env.fvo.get_free_variables
        mgr = self.env.formula_manager
        eq_preds: List[FNode] = []
        ineq_preds: List[FNode] = []
        curr_only: Set[FNode] = set()
        curr_next: Set[FNode] = set()
        next_only: Set[FNode] = set()
        # partition preds in eq_preds and ineq_preds.
        for s in impl.merge_ineqs(preds):
            assert not s.is_true()
            (eq_preds if s.is_equals() else ineq_preds).append(s)
        # process equalities first.
        while eq_preds:
            _pred = eq_preds.pop()
            assert len(self.env.ao.get_atoms(_pred)) == 1
            assert not _pred.is_true()
            assert not _pred.is_false()
            assert not _pred.is_not()
            assert self.cn(_pred) == _pred
            assert _pred.is_equals()
            pred = simpl(subst(_pred, eqs))
            if pred.is_false():
                return set([pred]), set(), set()
            if pred.is_true():
                continue
            symb, expr, is_next_s = eq2assign(self.env, pred,
                                              self.cn.td)
            if symb is not None:
                if symb.is_true():
                    continue
                if is_next_s:
                    assert isinstance(symb, FNode)
                    assert expr is not None
                    assert isinstance(expr, FNode)
                    assert symb.is_symbol()
                    if symb in eqs:
                        # symb = a & symb = b -> a = b
                        eq = self.cn(simpl(mgr.Equals(eqs[symb], expr)))
                        if not eq.is_true():
                            eq_preds.append(eq)
                    else:
                        # side-effect on eqs.
                        eqs[symb] = expr
                    continue
            symbs = get_free_vars(pred)
            if all(symb_is_curr(s) for s in symbs):
                curr_only.add(self.cn(pred))
            elif all(symb_is_next(s) for s in symbs):
                next_only.add(self.cn(pred))
            else:
                curr_next.add(self.cn(pred))
        for _pred in ineq_preds:
            assert len(self.env.ao.get_atoms(_pred)) == 1
            assert not _pred.is_true()
            assert not _pred.is_not()
            assert self.cn(_pred) == _pred
            assert _pred.is_lt() or _pred.is_le()
            pred = self.cn(simpl(subst(_pred, eqs)))
            if pred.is_false():
                return set([pred]), set(), set()
            if pred.is_true():
                continue
            symbs = get_free_vars(pred)
            if all(symb_is_curr(s) for s in symbs):
                curr_only.add(pred)
            elif all(symb_is_next(s) for s in symbs):
                next_only.add(pred)
            else:
                curr_next.add(pred)
        assert isinstance(curr_only, dict) or \
            all(self.cn(p) == p for p in curr_only)
        assert isinstance(curr_only, set) or \
            all(self.cn(p) == p for p in curr_only.keys())
        assert all(self.cn(p) == p for p in curr_next)
        assert all(self.cn(p) == p for p in next_only)
        if __debug__:
            # curr_only & curr_next & next_only & eqs <-> _orig
            mgr = self.env.formula_manager
            new = [c for c in curr_only]
            new.extend(curr_next)
            new.extend(next_only)
            new.extend(assigns2fnodes(self.env, eqs))
            from solver import Solver
            with Solver(self.env) as _solver:
                _solver.add_assertion(mgr.Not(mgr.Iff(mgr.And(_orig),
                                                      mgr.And(new))))
                assert _solver.solve() is False
        assert all(not p.is_true() for p in chain(curr_only, curr_next,
                                                  next_only))
        return curr_only, curr_next, next_only

    def back_prop(self, preds: Iterable[FNode], h_preds: Iterable[FNode],
                  impl: Implicant) -> Tuple[bool, Set[FNode], Set[FNode]]:
        """Learn equalities and backward propagate predicates."""
        assert all(self.env.fvo.get_free_variables(p) <= self.symbs
                   for p in preds)
        assert all(self.env.fvo.get_free_variables(p) <= self.symbs
                   for p in h_preds)
        assert isinstance(impl, Implicant)
        assert impl.env == self.env
        assert all(isinstance(s, set) for s in self.regs)
        assert all(isinstance(s, set) for s in self.h_regs)
        assert all(impl.cn(p) == p for reg in self.regs for p in reg)
        assert all(impl.cn(p) == p for reg in self.h_regs for p in reg)
        assert all(impl.cn(p) == p for tr in self.trans for p in tr)
        assert all(impl.cn(p) == p for tr in self.h_trans for p in tr)
        if __debug__:
            from itertools import tee
            preds, _preds = tee(preds, 2)
            _preds = list(_preds)
            assert all(impl.cn(p) == p for p in _preds)
            h_preds, _h_preds = tee(h_preds, 2)
            _h_preds = list(_h_preds)
            assert all(impl.cn(p) == p for p in _h_preds)
            _regs = [frozenset(reg) for reg in self.regs]
            _h_regs = [frozenset(h_reg) for h_reg in self.h_regs]
            _trans = [frozenset(tr) for tr in self.trans]
            _h_trans = [frozenset(tr) for tr in self.h_trans]
            _eqs = [dict(eq) for eq in self.t_eqs]
        false = self.env.formula_manager.FALSE()
        c_preds, cx_preds, res = \
            self.learn_eqs(chain((impl.cn(to_next(self.env, p, self.symbs))
                                  for p in preds),
                                 self.trans[-1]),
                           self.t_eqs[-1], impl)
        if false in c_preds:
            self.regs = [c_preds] * len(self)
            self.h_regs = [c_preds] * len(self)
            if __debug__:
                from solver import Solver
                with Solver(self.env) as _solver:
                    for t, (reg, h_reg, tr, h_tr, eq) in enumerate(zip(
                            _regs, _h_regs, _trans, _h_trans, _eqs)):
                        _solver.add_assertions(self.totime(p, t) for p in reg)
                        _solver.add_assertions(self.totime(p, t)
                                               for p in h_reg)
                        _solver.add_assertions(self.totime(p, t)
                                               for p in tr)
                        _solver.add_assertions(self.totime(p, t)
                                               for p in h_tr)
                        for p in assigns2fnodes(self.env, eq):
                            _solver.add_assertions(self.totime(p, t))
                    _solver.add_assertions(self.totime(p, len(_regs))
                                           for p in _preds)
                    _solver.add_assertions(self.totime(p, len(_regs))
                                           for p in _h_preds)
                    assert _solver.solve() is False
            return False, set(), set()
        self.trans[-1] = cx_preds
        c_h_preds, cx_preds, h_res = \
            self.learn_eqs(chain((to_next(self.env, p, self.symbs)
                                  for p in h_preds),
                                 self.h_trans[-1]),
                           self.t_eqs[-1], impl)
        if false in c_h_preds:
            self.regs = [c_preds] * len(self)
            self.h_regs = [c_preds] * len(self)
            if __debug__:
                from solver import Solver
                with Solver(self.env) as _solver:
                    for t, (reg, h_reg, tr, h_tr, eq) in enumerate(zip(
                            _regs, _h_regs, _trans, _h_trans, _eqs)):
                        _solver.add_assertions(self.totime(p, t) for p in reg)
                        _solver.add_assertions(self.totime(p, t)
                                               for p in h_reg)
                        _solver.add_assertions(self.totime(p, t)
                                               for p in tr)
                        _solver.add_assertions(self.totime(p, t)
                                               for p in h_tr)
                        for p in assigns2fnodes(self.env, eq):
                            _solver.add_assertions(self.totime(p, t))
                    _solver.add_assertions(self.totime(p, len(_regs))
                                           for p in _preds)
                    _solver.add_assertions(self.totime(p, len(_regs))
                                           for p in _h_preds)
                    assert _solver.solve() is False
            return False, set(), set()
        self.h_trans[-1] = cx_preds
        # iterate over regions and transitions in reverse order.
        for idx in range(len(self) - 1, 0, -1):
            t_idx = idx - 1
            c_preds, cx_preds, x_preds = \
                self.learn_eqs(chain((impl.cn(to_next(self.env, p, self.symbs))
                                      for p in self.regs[idx] | c_preds),
                                     self.trans[t_idx]),
                               self.t_eqs[t_idx], impl)
            if false in c_preds:
                self.regs = [c_preds] * len(self)
                self.h_regs = [c_preds] * len(self)
                if __debug__:
                    from solver import Solver
                    with Solver(self.env) as _solver:
                        for t, (reg, h_reg, tr, h_tr, eq) in enumerate(zip(
                                _regs, _h_regs, _trans, _h_trans, _eqs)):
                            _solver.add_assertions(self.totime(p, t) for p in reg)
                            _solver.add_assertions(self.totime(p, t)
                                                   for p in h_reg)
                            _solver.add_assertions(self.totime(p, t)
                                                   for p in tr)
                            _solver.add_assertions(self.totime(p, t)
                                                   for p in h_tr)
                            for p in assigns2fnodes(self.env, eq):
                                _solver.add_assertions(self.totime(p, t))
                        _solver.add_assertions(self.totime(p, len(_regs))
                                               for p in _preds)
                        _solver.add_assertions(self.totime(p, len(_regs))
                                               for p in _h_preds)
                        assert _solver.solve() is False
                return False, set(), set()
            self.regs[idx] = set(to_curr(self.env, p, self.symbs)
                                 for p in x_preds)
            self.trans[t_idx] = cx_preds
            c_h_preds, cx_preds, x_preds = \
                self.learn_eqs(chain((impl.cn(to_next(self.env, p, self.symbs))
                                      for p in self.h_regs[idx] | c_h_preds),
                                     self.h_trans[t_idx]),
                               self.t_eqs[t_idx], impl)
            if false in c_h_preds:
                self.regs = [c_preds] * len(self)
                self.h_regs = [c_preds] * len(self)
                if __debug__:
                    from solver import Solver
                    with Solver(self.env) as _solver:
                        for t, (reg, h_reg, tr, h_tr, eq) in enumerate(zip(
                                _regs, _h_regs, _trans, _h_trans, _eqs)):
                            _solver.add_assertions(self.totime(p, t) for p in reg)
                            _solver.add_assertions(self.totime(p, t)
                                                   for p in h_reg)
                            _solver.add_assertions(self.totime(p, t)
                                                   for p in tr)
                            _solver.add_assertions(self.totime(p, t)
                                                   for p in h_tr)
                            for p in assigns2fnodes(self.env, eq):
                                _solver.add_assertions(self.totime(p, t))
                        _solver.add_assertions(self.totime(p, len(_regs))
                                               for p in _preds)
                        _solver.add_assertions(self.totime(p, len(_regs))
                                               for p in _h_preds)
                        assert _solver.solve() is False
                return False, set(), set()
            self.h_regs[idx] = set(to_curr(self.env, p, self.symbs)
                                   for p in x_preds)
            self.h_trans[t_idx] = cx_preds
        self.regs[0].update(c_preds)
        self.h_regs[0].update(c_h_preds)
        res = set(to_curr(self.env, p, self.symbs) for p in res)
        h_res = set(to_curr(self.env, p, self.symbs) for p in h_res)
        if __debug__:
            # old & preds & h_preds <-> new.
            old = [self.totime(p, len(_regs))
                   for p in chain(_preds, _h_preds)]
            for t, (reg, h_reg, tr, h_tr, eq) in enumerate(zip(
                    _regs, _h_regs, _trans, _h_trans, _eqs)):
                old.extend(self.totime(p, t) for p in reg)
                old.extend(self.totime(p, t) for p in h_reg)
                old.extend(self.totime(p, t) for p in tr)
                old.extend(self.totime(p, t) for p in h_tr)
                old.extend(self.totime(p, t)
                           for p in assigns2fnodes(self.env, eq))
            new = [self.totime(p, len(self.regs))
                   for p in chain(res, h_res)]
            for t, (reg, h_reg, tr, h_tr, eq) in enumerate(zip(
                    self.regs, self.h_regs, self.trans, self.h_trans,
                    self.t_eqs)):
                new.extend(self.totime(p, t) for p in reg)
                new.extend(self.totime(p, t) for p in h_reg)
                new.extend(self.totime(p, t) for p in tr)
                new.extend(self.totime(p, t) for p in h_tr)
                new.extend(self.totime(p, t)
                           for p in assigns2fnodes(self.env, eq))
            from solver import Solver
            mgr = self.env.formula_manager
            with Solver(self.env) as _solver:
                _solver.add_assertion(mgr.Not(mgr.Iff(mgr.And(old), mgr.And(old))))
                assert _solver.solve() is False
            del old, new, mgr
            del _regs, _h_regs, _trans, _h_trans, _eqs, _preds, _h_preds

        assert all(self.env.fvo.get_free_variables(p) <= self.symbs
                   for p in chain(res, h_res))
        assert all(not p.is_true() for p in chain(res, h_res))
        # return predicates that we could not backward propagate.
        return (True, res, h_res)

    def enter_path(self, allow_params: bool) -> Iterator[Iterator[FNode]]:
        """Return symbolic representation of first iteration as
        sequence of ordered regs-steps. Last one is curr-only."""
        yield from (chain(reg, h_reg, assigns2fnodes(self.env, eq), tr, h_tr)
                    for reg, h_reg, eq, tr, h_tr in
                    zip(self.regs, self.h_regs, self.t_eqs,
                        self.trans, self.h_trans))
        yield iter([])

    def exit_path(self, allow_params: bool) -> Iterator[Iterator[FNode]]:
        """Return symbolic representation of last iteration as
        sequence of ordered regs-steps. Last one is curr-only."""
        yield from self.enter_path(allow_params)

    def rm_redundant(self, impl: Implicant) -> bool:
        """Remove redundant predicates, return False iff empty."""
        # First remove redundant preds from first region.
        # This is to avoid "forward" propagation of predicates.
        self.h_regs[0] = set(impl.rm_redundant_conjs(self.h_regs[0], {}))
        self.impl_reg = frozenset(impl.rm_redundant_conjs(self.impl_reg, {}))
        self.h_impl_reg = frozenset(impl.rm_redundant_conjs(self.h_impl_reg, {}))
        true = self.env.formula_manager.TRUE()
        assumes = {p: true for p in chain(self.h_regs[0], self.impl_reg,
                                          self.h_impl_reg)}
        self.regs[0] = set(impl.rm_redundant_conjs(self.regs[0], assumes))
        # Remove redundant preds from other regs and trans.
        # assume first reg, h_regs, h_trans and eqs.
        assumes = {self.totime(k, 0): v for k, v in assumes.items()}
        assumes.update((self.totime(p, 0), true)
                       for p in self.regs[0])
        assumes.update((self.totime(p, t), true)
                       for t, h_reg in enumerate(self.h_regs[1:], start=1)
                       for p in h_reg)
        assumes.update((self.totime(p, t), true)
                       for t, (h_tr, eq) in
                       enumerate(zip(self.h_trans, self.t_eqs))
                       for p in chain(h_tr, assigns2fnodes(self.env, eq)))

        preds = impl.rm_redundant_conjs(
            chain((impl.cn(self.totime(p, 0)) for p in self.trans[0]),
                  (impl.cn(self.totime(p, t))
                   for t, (reg, h_reg, tr, h_tr) in
                   enumerate(zip(self.regs[1:], self.h_regs[1:],
                                 self.trans[1:], self.h_trans[1:]),
                             start=1)
                   for p in chain(reg, h_reg, tr, h_tr))),
            assumes)
        # clear preds in regs, trans.
        for reg in self.regs[1:]:
            reg.clear()
        for tr in self.trans:
            tr.clear()
        # re-populate regs and trans from preds.
        for p in preds:
            assert not p.is_true()
            if p.is_false():
                return False
            assert self.cn(p) == p
            assert len(self.env.ao.get_atoms(p)) == 1
            assert len(self.env.fvo.get_free_variables(p)) >= 1
            is_next = get_times(self.env, p)
            assert len(is_next) in {1, 2}
            assert min(is_next) >= 0
            idx = min(is_next)
            assert max(is_next) <= idx + 1 <= len(self.regs)
            p = self.cn(self.totime(p, -idx - 1))
            assert len(get_times(self.env, p)) == 0
            if len(is_next) == 1:
                assert idx < len(self.regs)
                self.regs[idx].add(p)
            else:
                assert len(is_next) == 2
                self.trans[idx].add(p)
        return True

    def rm_deadlocks(self, preds: Iterable[FNode], impl: Implicant) -> int:
        """Strengthen regions by removing deadlocks."""
        regs = [[self.totime(p, 0)
                 for p in chain(self.regs[0], self.h_regs[0],
                                self.impl_reg, self.h_impl_reg)]]
        regs.extend([self.totime(p, idx) for p in chain(reg, h_reg)]
                    for idx, (reg, h_reg) in enumerate(zip(self.regs[1:],
                                                           self.h_regs[1:]),
                                                       start=1))
        regs.append([self.totime(p, len(self.regs)) for p in preds])
        trans = [[self.totime(p, idx)
                  for p in chain(tr, h_tr, assigns2fnodes(self.env, eq))]
                 for idx, (tr, h_tr, eq) in
                 enumerate(zip(self.trans, self.h_trans, self.t_eqs))]
        prefix = []
        num_refs = 0
        nnf = NNFizer(self.env).convert
        for idx in range(len(self.regs)):
            prefix.extend(regs[idx])
            for ref in impl.rm_deadlocks(prefix,
                                         chain(chain.from_iterable(trans[idx:]),
                                               chain.from_iterable(regs[idx+1:]))):
                assert isinstance(ref, FNode)
                if ref.is_false():
                    self.regs[0] = set([ref])
                    return -1
                assert len(get_times(self.env, ref)) == 1
                assert idx in get_times(self.env, ref)
                assert len(get_times(self.env, self.totime(ref, -idx - 1))) == 0
                assert all(symb_is_curr(s)
                           for s in self.env.fvo.get_free_variables(
                                   self.totime(ref, -idx - 1)))
                # TODO: use assignment to resolve disjunctions.
                ref = impl.cn(nnf(ref))
                if is_atom(ref) or ref.is_and():
                    stack = [ref]
                    ref = []
                    while stack:
                        curr = stack.pop()
                        if is_atom(curr):
                            ref.append(curr)
                        elif curr.is_and():
                            stack.extend(curr.args())
                    num_refs += len(ref)
                    self.regs[idx].update(impl.cn(self.totime(p, -idx - 1))
                                          for p in ref)
            prefix.extend(trans[idx])
        return num_refs

    def constrs(self, end: Iterable[FNode],
                h_end: Iterable[FNode]) -> Iterable[FNode]:
        """Return constraints for uapprox of self."""
        # u_reg & regs[0] & h_regs & eqs & u_eqs & h_trans & h_end ->
        # regs[1:] & trans & end.
        lhs = [self.totime(p, 0) for p in chain(self.u_reg, self.regs[0],
                                                self.impl_reg, self.h_impl_reg)]
        lhs.extend(self.totime(p, t)
                   for t, (h_reg, eq, u_eq, h_tr) in enumerate(zip(
                           self.h_regs, self.t_eqs, self.u_eqs, self.h_trans))
                   for p in chain(h_reg, h_tr, assigns2fnodes(self.env, eq),
                                  assigns2fnodes(self.env, u_eq)))
        lhs.extend(self.totime(p, len(self)) for p in h_end)
        rhs = [self.totime(p, 0) for p in self.trans[0]]
        rhs.extend(self.totime(p, t)
                   for t, (reg, tr) in enumerate(
                           zip(self.regs[1:], self.trans[1:]),
                           start=1)
                   for p in chain(reg, tr))
        rhs.extend(self.totime(p, len(self)) for p in end)
        mgr = self.env.formula_manager
        yield mgr.Implies(mgr.And(lhs), mgr.And(rhs))

    def dnf_constrs(self, end: Iterable[FNode],
                    h_end: Iterable[FNode]) -> Iterator[Iterator[FNode]]:
        """Return negation of constraints for uapprox of self in DNF."""
        # lhs: u_reg & regs[0] & h_regs & eqs & u_eqs & h_trans & h_end
        # rhs: regs[1:] & trans & end.
        lhs = [self.totime(p, 0) for p in chain(self.u_reg, self.regs[0],
                                                self.impl_reg, self.h_impl_reg)]
        lhs.extend(self.totime(p, t)
                   for t, (h_reg, eq, u_eq, h_tr) in enumerate(zip(
                           self.h_regs, self.t_eqs, self.u_eqs, self.h_trans))
                   for p in chain(h_reg, h_tr, assigns2fnodes(self.env, eq),
                                  assigns2fnodes(self.env, u_eq)))
        lhs.extend(self.totime(p, len(self)) for p in h_end)

        yield from (chain(lhs, [np])
                    for p in self.trans[0]
                    for np in not_rels(self.env, self.totime(p, 0)))

        yield from (chain(lhs, [np])
                    for idx, (reg, tr) in enumerate(
                            zip(self.regs[1:], self.trans[1:]),
                            start=1)
                    for p in chain(reg, tr)
                    for np in not_rels(self.env, self.totime(p, idx)))
        yield from (chain(lhs, [np])
                    for p in end
                    for np in not_rels(self.env, self.totime(p, len(self))))


class RFFunnel(Funnel):
    """Funnel representing a bounded loop over a Funnel"""
    def __init__(self, env: PysmtEnv, first_idx: int,
                 symbs: FrozenSet[FNode],
                 states: List[Dict[FNode, FNode]],
                 assigns: List[Dict[FNode, FNode]],
                 regions: List[Set[FNode]],
                 t_eqs: List[Dict[FNode, FNode]],
                 trans: List[Set[FNode]],
                 h_regions: List[Set[FNode]],
                 h_trans: List[Set[FNode]],
                 totime: ExprAtTime, cn: Canonizer,
                 rf: Optional[RankFun] = None):
        super().__init__(env, first_idx, symbs, states, assigns, regions,
                         t_eqs, trans, h_regions, h_trans, totime, cn)
        if rf is not None:
            assert isinstance(rf, RankFun)
            assert rf.env == env
            self.rf = rf
            self.params = set(self.rf.params)
        else:
            if self.real_symbs:
                expr, params = linear_comb(env, self.same_type_symbs)
                delta = new_param(env, "d", PyReal)
                params.add(delta)
                self.rf: RankFun = RRankFun(env, self.same_type_symbs, expr,
                                            delta, params)
            else:
                assert all(s.symbol_type().is_int_type() for s in self.symbs)
                expr, params = linear_comb(env, self.int_symbs)
                self.rf = IRankFun(env, self.int_symbs, expr, params)
            self.params.update(params)
            self.rf.canonize(cn)

    def instantiate(self, model: Dict[FNode, FNode]) -> None:
        """Replace all parameters according to `model`"""
        assert self.params <= frozenset(model.keys())
        super().instantiate(model)
        self.rf = self.rf.instantiate(model)

    def filter_constant_symbs(self, lasso_symbs: FrozenSet[FNode],
                              last_state: Dict[FNode, FNode],
                              last_reg: Set[FNode],
                              last_h_reg: Set[FNode]) -> FrozenSet[FNode]:
        if len(lasso_symbs) == 0:
            return lasso_symbs
        mgr = self.env.formula_manager
        assertions = [self.totime(p, idx)
                      for idx, (reg, h_reg, eq, tr, h_tr) in
                      enumerate(zip(self.regs, self.h_regs, self.t_eqs,
                                    self.trans, self.h_trans))
                      for p in chain(reg, h_reg, tr, h_tr,
                                     assigns2fnodes(self.env, eq))]
        # RFFunnel either loop-back or move to next.
        assertions.append(self.totime(
            mgr.Or(mgr.And(chain(last_reg, last_h_reg)),
                   mgr.And(chain(self.regs[0], self.h_regs[0]))),
            len(self.regs)))
        res = []
        lasso_symbs = list(lasso_symbs)
        with MultiSolver(self.env, Funnel.get_const_symbs_timeout(),
                         log_lvl=Funnel.get_log_lvl(),
                         solver_names=["msat"]) as solver:
            solver.add_assertions(assertions)
            solver.push()
            while len(lasso_symbs) > 0:
                assert solver.assertions == assertions
                s = lasso_symbs.pop()
                curr_assign = mgr.Equals(self.totime(s, 0), self.states[0][s])
                # unsat (states & trans & s_0 = v_0 & !(/\ s_i = v_i))
                solver.add_assertion(curr_assign)
                solver.push()
                solver.add_assertion(mgr.Not(mgr.And(
                    mgr.Equals(self.totime(s, idx + 1), x_step[s])
                    for idx, x_step in enumerate(self.states[1:]))))
                try:
                    sat = solver.solve()
                except SolverReturnedUnknownResultError:
                    sat = None
                    solver.reset_assertions()
                    solver.add_assertions(assertions)
                    solver.push()
                    solver.add_assertion(curr_assign)
                    solver.push()
                solver.pop()  # leave: assertions & curr_assign
                if sat is False:
                    # reg0' -> state0'; last_reg' -> last_state'
                    for reg, h_reg, state in [(self.regs[0], self.h_regs[0], self.states[0]),
                                              (last_reg, last_h_reg, last_state)]:
                        solver.push()
                        solver.add_assertions(self.totime(p, len(self.regs))
                                              for p in chain(reg, h_reg))
                        solver.add_assertion(mgr.Not(
                            mgr.Equals(self.totime(s, len(self.regs)),
                                       state[s])))
                        try:
                            sat = solver.solve()
                        except SolverReturnedUnknownResultError:
                            sat = None
                            solver.reset_assertions()
                            solver.add_assertions(assertions)
                            solver.push()
                            solver.add_assertion(curr_assign)
                            solver.push()
                        solver.pop()
                        if sat is not False:
                            break
                solver.pop()
                assert solver.assertions == assertions
                if sat is False:
                    res.append(s)
                    eq = mgr.Equals(self.totime(s, len(self.regs)), last_state[s])
                    solver.add_assertion(eq)
                    assertions.append(eq)
                    for idx, step in enumerate(self.states):
                        eq = mgr.Equals(self.totime(s, idx), step[s])
                        solver.add_assertion(eq)
                        assertions.append(eq)
                solver.push()
        if __debug__:
            from solver import Solver
            assertions = [self.totime(p, idx)
                          for idx, (reg, h_reg, eq, tr, h_tr) in
                          enumerate(zip(self.regs, self.h_regs, self.t_eqs,
                                        self.trans, self.h_trans))
                          for p in chain(reg, h_reg, tr, h_tr,
                                         assigns2fnodes(self.env, eq))]
            assertions.extend(assign2fnode(self.env, self.totime(s, 0),
                                           self.states[0][s])
                              for s in res)
            disj = []
            for idx, x_step in enumerate(self.states[1:]):
                for s in res:
                    eq = assign2fnode(self.env, self.totime(s, idx + 1),
                                      x_step[s])
                    disj.append(eq)
            # check validity of constant symbs.
            with Solver(env=self.env) as _solver:
                _solver.add_assertions(assertions)
                # reg[0]' & h_reg[0]'
                _solver.add_assertions(self.totime(p, len(self.regs))
                                       for p in chain(self.regs[0], self.h_regs[0]))
                _disj = list(disj)
                # state[0]'
                _disj.extend(assign2fnode(self.env,
                                          self.totime(s, len(self.regs)),
                                          self.states[0][s])
                             for s in res)
                _solver.add_assertion(mgr.Not(mgr.And(_disj)))
                assert _solver.solve() is False
            with Solver(env=self.env) as _solver:
                _solver.add_assertions(assertions)
                # last_reg' & last_h_reg'
                _solver.add_assertions(self.totime(p, len(self.regs))
                                       for p in chain(last_reg, last_h_reg))
                _disj = list(disj)
                _disj.extend(assign2fnode(self.env,
                                          self.totime(s, len(self.regs)),
                                          last_state[s])
                             for s in res)
                _solver.add_assertion(mgr.Not(mgr.And(_disj)))
                assert _solver.solve() is False

        return frozenset(res)

    def mk_symbs_constant(self, symbs: FrozenSet[FNode],
                          last_state: Dict[FNode, FNode]) -> None:
        if len(symbs & self.symbs) == 0:
            return
        super().mk_symbs_constant(symbs, last_state)
        if len(self.rf.params) == 0:
            self.rf.mk_symbs_constant(symbs, {s: self.states[0][s]
                                              for s in symbs})
        else:
            self.params -= self.rf.params
            if self.real_symbs:
                expr, params = linear_comb(self.env, self.same_type_symbs)
                delta = new_param(self.env, "d", PyReal)
                params.add(delta)
                self.rf: RankFun = RRankFun(self.env, self.same_type_symbs, expr,
                                            delta, params)
            else:
                assert all(s.symbol_type().is_int_type() for s in self.symbs)
                expr, params = linear_comb(self.env, self.int_symbs)
                self.rf = IRankFun(self.env, self.int_symbs, expr, params)
            self.params.update(params)
            self.rf.canonize(self.cn)

    def first(self) -> Iterable[FNode]:
        return chain(super().first(), [self.rf.is_ranked()])

    def back_prop(self, preds: Iterable[FNode], h_preds: Iterable[FNode],
                  impl: Implicant) -> Tuple[bool, Set[FNode], Set[FNode]]:
        assert all(self.env.fvo.get_free_variables(p) <= self.symbs
                   for p in preds)
        assert all(self.env.fvo.get_free_variables(p) <= self.symbs
                   for p in h_preds)
        assert isinstance(impl, Implicant)
        assert impl.env == self.env
        res, keep = self._split_rev_inductive_preds(preds)
        h_res, h_keep = self._split_rev_inductive_preds(h_preds)
        # propagate res and h_res.
        not_empty, in_keep, in_h_keep = super().back_prop(res, h_res, impl)

        assert all(self.env.fvo.get_free_variables(p) <= self.symbs
                   for p in chain(keep, in_keep, h_keep, in_h_keep))
        assert all(not p.is_true()
                   for p in chain(keep, in_keep, h_keep, in_h_keep))
        return not_empty, keep | in_keep, h_keep | in_h_keep

    def _split_rev_inductive_preds(self, preds: Iterable[FNode]) -> \
            Tuple[Set[FNode], Set[FNode]]:
        """Partition preds in reverse-inductive and non-reverse inductive.
        Reverse-inductive(p) := t & p' -> p"""
        assert len(self.trans) > 0
        assert len(self.trans) == len(self.regs)
        assert len(self.t_eqs) == len(self.trans)
        assert len(self.h_regs) == len(self.regs)
        assert len(self.h_trans) == len(self.h_regs)
        assert all(symb_is_curr(s) for p in preds
                   for s in self.env.fvo.walk(p))
        assert all(not p.is_true() for p in preds)
        assert all(not p.is_false() for p in preds)
        mgr = self.env.formula_manager
        invar = set()
        not_invar = set()
        idx = 0
        with MultiSolver(self.env, Funnel.get_propagate_timeout(),
                         log_lvl=Funnel.get_log_lvl(),
                         solver_names=["msat"]) as solver:
            assertions: List[FNode] = []
            for idx, (assign, reg, h_reg, eqs, trans, h_trans) in enumerate(
                    zip(self.assigns, self.regs, self.h_regs,
                        self.t_eqs, self.trans, self.h_trans)):
                # add constant assignments, region, h_region, eqs, trans and h_trans.
                assertions.extend(self.totime(p, idx) for p in chain(
                    reg, h_reg, assigns2fnodes(self.env, assign),
                    assigns2fnodes(self.env, eqs), trans, h_trans))
            idx += 1
            assert idx == len(self.trans)
            solver.add_assertions(assertions)
            # Valid(path & p' -> p) <==> Unsat(path & p' & !p)
            for p in preds:
                solver.push()
                # holds at the end.
                solver.add_assertion(self.totime(p, idx))
                # false at the beginning.
                solver.add_assertion(mgr.Not(self.totime(p, 0)))
                sat = None
                try:
                    sat = solver.solve()
                except SolverReturnedUnknownResultError:
                    sat = None
                    solver.reset_assertions()
                    solver.add_assertions(assertions)
                    solver.push()
                solver.pop()
                if sat is False:
                    invar.add(p)
                else:
                    not_invar.add(p)

        assert all(symb_is_curr(s) for p in invar
                   for s in self.env.fvo.walk(p))
        assert all(symb_is_curr(s) for p in not_invar
                   for s in self.env.fvo.walk(p))
        assert all(self.cn(p) == p for p in invar)
        assert all(self.cn(p) == p for p in not_invar)
        if __debug__:
            # path & invar' -> invar
            from solver import Solver
            path = [self.totime(p, len(self.regs)) for p in invar]
            for t, (assign, reg, h_reg, eqs, trans, h_trans) in enumerate(
                    zip(self.assigns, self.regs, self.h_regs,
                        self.t_eqs, self.trans, self.h_trans)):
                path.extend(self.totime(p, t) for p in reg)
                path.extend(self.totime(p, t) for p in h_reg)
                path.extend(self.totime(p, t) for p in trans)
                path.extend(self.totime(p, t) for p in h_trans)
                path.extend(self.totime(p, t)
                            for p in assigns2fnodes(self.env, assign))
                path.extend(self.totime(p, t)
                            for p in assigns2fnodes(self.env, eqs))
            mgr = self.env.formula_manager
            for p in invar:
                with Solver(self.env) as _solver:
                    _solver.add_assertions(path)
                    _solver.add_assertion(mgr.Not(self.totime(p, 0)))
                    assert _solver.solve() is False
        return invar, not_invar

    def write_hr(self, idx: int, buf: StringIO) -> int:
        assert isinstance(buf, StringIO)
        assert isinstance(idx, int)
        serialize = self.env.serializer.serialize
        simpl = self.env.simplifier.simplify
        buf.write(f"\tWhile {serialize(simpl(self.rf.is_ranked()))},"
                  f" do {idx} -- {idx + len(self.trans) - 1}\n")
        idx = super().write_hr(idx, buf)
        buf.write("\tEnd While\n")
        return idx

    def _path(self, allow_params: bool) -> Iterator[Iterator[FNode]]:
        idx = 0
        if allow_params or len(self.rf.params) == 0:
            yield chain([self.rf.is_ranked()], self.regs[0], self.h_regs[0],
                        assigns2fnodes(self.env, self.t_eqs[0]), self.trans[0],
                        self.h_trans[0])
            idx += 1
        yield from (chain(reg, h_reg, assigns2fnodes(self.env, eq), tr, h_tr)
                    for reg, h_reg, eq, tr, h_tr in
                    zip(self.regs[idx:], self.h_regs[idx:], self.t_eqs[idx:],
                        self.trans[idx:], self.h_trans[idx:]))

    def enter_path(self, allow_params: bool) -> Iterator[Iterator[FNode]]:
        """Return symbolic representation of first iteration as sequence of
        ordered steps. Last step is curr-only."""
        yield from self._path(allow_params)
        yield iter([])

    def loop_path(self, allow_params: bool) -> Iterator[Iterator[FNode]]:
        """Return symbolic representation of iteration different from
        last one as sequence of ordered steps. Last step is curr-only"""
        yield from self._path(allow_params)
        yield chain([self.rf.is_ranked()] if allow_params or
                    len(self.rf.params) == 0 else [],
                    self.regs[0], self.h_regs[0])

    def exit_path(self, allow_params: bool) -> Iterator[Iterator[FNode]]:
        """Return symbolic representation of last iteration as
        sequence of ordered regs-steps. Last one is curr-only."""
        yield from self._path(allow_params)
        yield iter([self.rf.is_min()] if allow_params or len(self.rf.params) == 0
                   else [])

    def inst_rf(self, end: Iterable[FNode],
                impl: Implicant) -> Optional[RankFun]:
        assert isinstance(end, (list, set, frozenset))
        assert len(end) == len(frozenset(end))
        model = None
        if Funnel.get_use_ef():
            model, _ = efmultisolve(self.env, self.rf.params, None,
                                    self._rf_constrs(end),
                                    impl=impl)
        if model is None and Funnel.get_use_motzkin():
            delta = self.rf.delta if isinstance(self.rf, RRankFun) else None
            model = motzkin_solve(self.env, self.params,
                                  self._rf_dnf(end),
                                  self.cn.td, delta)
        if model is not None and model is not False:
            assert isinstance(model, dict)
            assert self.rf.params <= model.keys()
            self.rf = self.rf.instantiate(model)
            return self.rf
        return None

    def _rf_constrs(self, reg_end: Iterable[FNode]) -> FNode:
        """Return constraints that must be valid for self.rf:
        (path & rf' > 0 -> reg0' & rf' < rf)
        (path & rf' <= 0 -> reg_end')
        equiv to:
        path -> (rf' > 0 & reg0' & rf' < rf) | (rf' <= 0 & reg_end')
        """
        mgr = self.env.formula_manager
        path = mgr.And(self.totime(p, t)
                       for t, steps in enumerate(self._path(False))
                       for p in steps)
        x_t = len(self)
        assert all(t <= x_t for t in get_times(self.env, path))
        assert any(t == x_t for t in get_times(self.env, path))
        # rf' > 0 & reg0' & rf' < rf
        lback = mgr.And(self.totime(self.rf.is_ranked(), x_t),
                        self.totime(self.rf.is_decr(), 0, x_t),
                        *(self.totime(p, x_t) for p in
                          chain(self.regs[0], self.h_regs[0])))
        # rf' <= 0 & reg_end'
        end = mgr.And(self.totime(self.rf.is_min(), x_t),
                      *(self.totime(p, x_t) for p in reg_end))
        return mgr.Implies(path, mgr.Or(lback, end))

    def _rf_dnf(self, reg_end: Iterable[FNode]) -> Iterator[Iterator[FNode]]:
        """Return negation of constraints that must be valid for self.rf
        in dnf.
        Negation of:
        (path & rf' > 0 -> reg0' & rf' < rf) & (path & rf' <= 0 -> reg_end')
        ==>
        (path & rf' > 0 & rf' >= rf) |
        \/p in reg0: (path & rf' > 0 & !p') |
        \/p in reg_end: (path & rf' <= 0 & !p')
        """
        path = [self.totime(p, t) for t, step in enumerate(self._path(False))
                for p in step]
        x_t = len(self)
        # path & rf' > 0 & rf' >= rf
        ranked_path = list(path)
        ranked_path.append(self.totime(self.rf.is_ranked(), x_t))
        yield chain(ranked_path,
                    [self.totime(not_rel(self.env, self.rf.is_decr()),
                                 0, x_t)])
        # \/p in reg0: (path & rf' > 0 & !p')
        yield from (chain(ranked_path, [np])
                    for p in chain(self.regs[0], self.h_regs[0])
                    for np in not_rels(self.env, self.totime(p, x_t)))
        # \/p in reg_end: (path & rf' <= 0 & !p')
        min_path = list(path)
        min_path.append(self.totime(self.rf.is_min(), x_t))
        yield from (chain(min_path, [np])
                    for p in reg_end
                    for np in not_rels(self.env, self.totime(p, x_t)))

    def constrs(self, end: Iterable[FNode],
                h_end: Iterable[FNode]) -> Iterable[FNode]:
        """Return constraints for uapprox of self."""
        # rf > 0 & u_reg & regs[0] & h_regs & eqs & u_eqs & h_trans ->
        # regs[1:] & trans &
        #   (rf' > 0 & h_regs[0]' -> rf' < rf & u_reg' & regs[0]') &
        #   (rf' = 0 & h_end' -> end')
        lhs = [self.totime(p, 0)
               for p in chain(self.u_reg, self.regs[0], [self.rf.is_ranked()],
                              self.impl_reg, self.h_impl_reg)]
        lhs.extend(self.totime(p, t)
                   for t, (h_reg, eq, u_eq, h_tr) in enumerate(zip(
                           self.h_regs, self.t_eqs, self.u_eqs, self.h_trans))
                   for p in chain(h_reg, h_tr, assigns2fnodes(self.env, eq),
                                  assigns2fnodes(self.env, u_eq)))
        rhs = [self.totime(tr, 0) for tr in self.trans[0]]
        rhs.extend(self.totime(p, t)
                   for t, (reg, tr) in enumerate(zip(self.regs[1:],
                                                     self.trans[1:]),
                                                 start=1)
                   for p in chain(reg, tr))
        last = len(self)
        mgr = self.env.formula_manager
        lback_lhs = [self.totime(p, last) for p in self.h_regs[0]]
        lback_lhs.append(self.totime(self.rf.is_ranked(), last))
        lback_rhs = [self.totime(p, last)
                     for p in chain(self.u_reg, self.regs[0])]
        lback_rhs.append(self.totime(self.rf.is_decr(), 0, last))
        rhs.append(mgr.Implies(mgr.And(lback_lhs), mgr.And(lback_rhs)))

        exit_lhs = [self.totime(p, last) for p in h_end]
        exit_lhs.append(self.totime(self.rf.is_min(), last))
        exit_rhs = mgr.And(self.totime(p, last) for p in end)
        rhs.append(mgr.Implies(mgr.And(exit_lhs), exit_rhs))
        return [mgr.Implies(mgr.And(lhs), mgr.And(rhs))]

    def dnf_constrs(self, end: Iterable[FNode],
                    h_end: Iterable[FNode]) -> Iterator[Iterator[FNode]]:
        """Return negation of constraints for uapprox of self in DNF."""
        # lhs: rf > 0 & u_reg & regs[0] & h_regs & eqs & u_eqs & h_trans
        # rhs: regs[1:] & trans
        lhs = [self.totime(p, 0)
               for p in chain(self.u_reg, self.regs[0], [self.rf.is_ranked()],
                              self.impl_reg, self.h_impl_reg)]
        lhs.extend(self.totime(p, t)
                   for t, (h_reg, eq, u_eq, h_tr) in enumerate(zip(
                           self.h_regs, self.t_eqs, self.u_eqs, self.h_trans))
                   for p in chain(h_reg, h_tr, assigns2fnodes(self.env, eq),
                                  assigns2fnodes(self.env, u_eq)))

        yield from (chain(lhs, [np])
                    for p in self.trans[0]
                    for np in not_rels(self.env, self.totime(p, 0)))

        yield from (chain(lhs, [np])
                    for idx, (reg, tr) in enumerate(
                            zip(self.regs[1:], self.trans[1:]),
                            start=1)
                    for p in chain(reg, tr)
                    for np in not_rels(self.env, self.totime(p, idx)))
        last = len(self)
        # lback := rf' > 0 & h_regs[0]'
        # rhs := rf' < rf & u_reg' & regs[0]'
        lback_lhs = [self.totime(p, last) for p in self.h_regs[0]]
        lback_lhs.append(self.totime(self.rf.is_ranked(), last))
        # (lhs & lback) -> rf' < rf
        yield chain(lhs, lback_lhs,
                    [self.totime(not_rel(self.env, self.rf.is_decr()),
                                 0, last)])
        # (lhs & lback) -> u_reg' & regs[0]'
        yield from (chain(lhs, lback_lhs, [np])
                    for p in chain(self.u_reg, self.regs[0])
                    for np in not_rels(self.env, self.totime(p, last)))
        # exit := rf' = 0 & h_end'
        # rhs := end
        exit_lhs = [self.totime(p, last) for p in h_end]
        exit_lhs.append(self.totime(self.rf.is_min(), last))
        # (lhs & exit) -> end
        yield from (chain(lhs, exit_lhs, [np])
                    for p in end
                    for np in not_rels(self.env, self.totime(p, last)))

    def rm_deadlocks(self, preds: Iterable[FNode],
                     impl: Implicant) -> int:
        """Strengthen regions by removing deadlocks"""
        mgr = self.env.formula_manager
        regs = [[self.totime(p, 0)
                 for p in chain(self.regs[0], self.h_regs[0],
                                self.impl_reg, self.h_impl_reg)]]
        regs.extend([self.totime(p, idx) for p in chain(reg, h_reg)]
                    for idx, (reg, h_reg) in enumerate(zip(self.regs[1:],
                                                           self.h_regs[1:]),
                                                       start=1))
        regs.append([mgr.Or(
            mgr.And(self.totime(p, len(self.regs)) for p in preds),
            mgr.And(self.totime(p, len(self.regs))
                    for p in chain(self.regs[0], self.h_regs[0]))
            )])
        trans = [[self.totime(p, idx)
                  for p in chain(tr, h_tr, assigns2fnodes(self.env, eq))]
                 for idx, (tr, h_tr, eq) in
                 enumerate(zip(self.trans, self.h_trans, self.t_eqs))]
        prefix = []
        num_refs = 0
        nnf = NNFizer(self.env).convert
        for idx in range(len(self.regs)):
            prefix.extend(regs[idx])
            for ref in impl.rm_deadlocks(prefix,
                                         chain(chain.from_iterable(trans[idx:]),
                                         chain.from_iterable(regs[idx+1:]))):
                assert isinstance(ref, FNode)
                if ref.is_false():
                    self.regs[0] = set([ref])
                    return -1
                assert len(get_times(self.env, ref)) == 1
                assert idx in get_times(self.env, ref)
                assert len(get_times(self.env, self.totime(ref, -idx - 1))) == 0
                assert all(symb_is_curr(s)
                           for s in self.env.fvo.get_free_variables(
                                   self.totime(ref, -idx - 1)))
                # TODO: use assignment to resolve disjunctions.
                ref = impl.cn(nnf(ref))
                if is_atom(ref) or ref.is_and():
                    stack = [ref]
                    ref = []
                    while stack:
                        curr = stack.pop()
                        assert isinstance(curr, FNode)
                        if is_atom(curr):
                            ref.append(curr)
                        elif curr.is_and():
                            stack.extend(curr.args())
                    num_refs += len(ref)
                    self.regs[idx].update(impl.cn(self.totime(p, -idx - 1))
                                          for p in ref)
        return num_refs
