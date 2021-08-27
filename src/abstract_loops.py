from typing import Iterator, Tuple, List, Optional, Union, Dict, FrozenSet
from itertools import count, chain
from enum import IntEnum

from pysmt.fnode import FNode
import pysmt.typing as types
from pysmt.environment import Environment as PysmtEnv
from pysmt.exceptions import SolverReturnedUnknownResultError

from utils import symb_to_next, to_next, to_curr, log, assign2fnodes, new_symb
from multisolver import MultiSolver
from canonize import Canonizer
from rewritings import TimesDistributor
from expr_at_time import ExprAtTime
from generalise import Generaliser
from rankfun import RankFun
from hint import Hint, TransType


class HintMode(IntEnum):
    MAY = 0
    MUST = 1
    ALL = 2


class BMC:
    """Iterate over abstract loops via BMC"""

    _LOG_LVL = 1
    _PRED_MONITOR_STR = "_bmc"
    _TIMEOUT = 30
    _MAX_K = -1
    _HINT_MODE = HintMode.MUST

    @staticmethod
    def set_timeout(value: int) -> None:
        assert isinstance(value, int)
        BMC._TIMEOUT = value

    @staticmethod
    def get_timeout() -> int:
        return BMC._TIMEOUT

    @staticmethod
    def set_max_k(val: int) -> None:
        assert val is None or isinstance(val, int)
        BMC._MAX_K = val

    @staticmethod
    def get_max_k() -> int:
        return BMC._MAX_K

    @staticmethod
    def get_hints_mode() -> HintMode:
        return BMC._HINT_MODE

    @staticmethod
    def set_hints_mode(val: HintMode) -> None:
        assert isinstance(val, HintMode)
        BMC._HINT_MODE = val

    def __init__(self, env: PysmtEnv, init: FNode, trans: FNode, fair: FNode,
                 hints: FrozenSet[Hint], all_symbs: FrozenSet[FNode]):
        assert isinstance(env, PysmtEnv)
        assert isinstance(init, FNode)
        assert isinstance(trans, FNode)
        assert isinstance(fair, FNode)
        assert isinstance(hints, frozenset)
        assert all(isinstance(h, Hint) for h in hints)
        assert all(h0 is h1 or h0.name != h1.name
                   for h0 in hints for h1 in hints)
        assert isinstance(all_symbs, frozenset)
        assert all(isinstance(s, FNode) for s in all_symbs)
        assert all(s in env.formula_manager.get_all_symbols()
                   for s in all_symbs)

        self.o_env = env
        self.o_mgr = env.formula_manager
        self.o_norm = self.o_mgr.normalize
        self.i_env = PysmtEnv()
        self.i_mgr = self.i_env.formula_manager
        self.i_norm = self.i_mgr.normalize
        i_get_free_vars = self.i_env.fvo.get_free_variables
        i_get_atoms = self.i_env.ao.get_atoms
        self.totime = ExprAtTime(self.i_env,
                                 ignore_pref=BMC._PRED_MONITOR_STR)
        self.td = TimesDistributor(self.i_env)
        self.cn = Canonizer(env=self.i_env)
        self.generaliser = Generaliser(self.i_env, self.cn, self.totime)
        self.hints = [h.to_env(self.i_env) for h in hints]
        self.hint_active = [self._fresh_symb(f"{BMC._PRED_MONITOR_STR}_{h.name}")
                            for h in self.hints]
        hints_ts = [h.get_trans_system(active)
                    for h, active in zip(self.hints, self.hint_active)]
        hint_loc_active = [active for (_, _, _, active) in hints_ts]

        # hint_active symbs must be frozen.
        assert all(self.totime(s, 5) == s for s in self.hint_active)
        self.hint_symbs = frozenset(
            chain.from_iterable(symbs for (symbs, _, _, _) in hints_ts))
        self.orig_symbs = frozenset(self.i_norm(s) for s in all_symbs)
        self.all_symbs = frozenset.union(self.hint_symbs, self.orig_symbs,
                                         self.hint_active)
        # init of transition system.
        self.init = [self.i_norm(init)]
        # init of Hints encoding
        self.init.extend(chain.from_iterable(
            hint_init for (_, hint_init, _, _) in hints_ts))
        self._orig_trans = self.i_norm(trans)
        self.trans = [self._orig_trans]
        self.trans.extend(chain.from_iterable(
            hint_trans for (_, _, hint_trans, _) in hints_ts))
        assert all(isinstance(t, FNode) for t in self.trans)
        fair = self.cn(self.i_norm(fair))
        assert fair in self.i_mgr.formulae.values()
        assert all(s in self.i_mgr.get_all_symbols()
                   for s in i_get_free_vars(fair))
        assert all(s in self.i_mgr.get_all_symbols()
                   for s in self.orig_symbs)
        assert i_get_free_vars(fair) <= self.orig_symbs
        assert all(i_get_free_vars(t) <= self.all_symbs |
                   frozenset(symb_to_next(self.i_mgr, s)
                             for s in self.all_symbs)
                   for t in self.trans)

        # collect atoms for abstract loop-back detection.
        lback_atms = set()
        for pred in chain(i_get_atoms(fair),
                          (self.cn(p) for c_init in self.init
                           for p in i_get_atoms(c_init)
                           if i_get_free_vars(p) <= self.orig_symbs)):
            assert i_get_free_vars(pred) <= self.orig_symbs
            assert self.cn(pred) == pred
            lback_atms.add(pred)
            if pred.is_equals():
                lt_pred = self.cn(self.i_mgr.LT(pred.arg(0), pred.arg(1)))
                lback_atms.add(lt_pred)
        for pred in chain.from_iterable(i_get_atoms(t) for t in self.trans):
            free_v = i_get_free_vars(pred)
            intsec_size = len(free_v & self.all_symbs)
            # either all current or all next.
            if intsec_size == len(free_v) or intsec_size == 0:
                pred = to_curr(self.i_mgr, pred, self.all_symbs) \
                    if intsec_size == 0 else pred
                pred = self.cn(pred)
                lback_atms.add(pred)
                if pred.is_equals():
                    lt_pred = self.cn(self.i_mgr.LT(pred.arg(0), pred.arg(1)))
                    lback_atms.add(lt_pred)
        assert all(i_get_free_vars(s) <= self.all_symbs
                   for s in lback_atms)
        assert all(self.cn(atm) == atm for atm in lback_atms)
        assert all(a.is_theory_relation() or
                   (a.is_symbol() and a.symbol_type().is_bool_type())
                   for a in lback_atms)

        if self.hints:
            # active Hints must have disjoint symbols.
            self.init.extend(Hint.disjoint_symbs(self.i_env, self.hints,
                                                 self.hint_active))
            # invariant: minimise 1 ranking function at a time.
            at_most_1_ranked = list(Hint.at_most_1_ranked(self.i_env, self.hints,
                                                          self.hint_active))
            self.init.extend(at_most_1_ranked)
            self.trans.extend(to_next(self.i_mgr, pred, self.all_symbs)
                              for pred in at_most_1_ranked)
            # add constraint corresponding to hint encoding mode.
            if BMC.get_hints_mode() is HintMode.MUST:
                self.init.append(self.i_mgr.Or(self.hint_active))
            elif BMC.get_hints_mode() is HintMode.ALL:
                self.init.append(self.i_mgr.And(self.hint_active))
            else:
                assert BMC.get_hints_mode() is HintMode.MAY

        self.symb2monitor = \
            {s: self._fresh_symb(f"{BMC._PRED_MONITOR_STR}_{s.symbol_name()}",
                                 m_type=s.symbol_type())
             for s in chain(self.orig_symbs, self.hint_symbs)}
        # self.rank_funs: List[RankFun] = []
        self._new_rank_fun = False

        subst = self.i_env.substituter.substitute
        self._in_loop = self._fresh_symb("inloop")

        self.init.append(self.i_mgr.Not(self._in_loop))
        # loop begins if all(symb == monitor) & all(h_active -> h_loc_active)
        start_loop = self.i_mgr.And(
            chain(assign2fnodes(self.i_env, self.symb2monitor),
                  (self.i_mgr.Implies(h_act, h_loc_act)
                   for h_act, h_loc_act in zip(self.hint_active,
                                               hint_loc_active))))
        if __debug__:
            self.start_loop = start_loop

        self.trans.append(
            self.i_mgr.Implies(symb_to_next(self.i_mgr, self._in_loop),
                               self.i_mgr.Or(self._in_loop, start_loop)))
         # self.trans.append(
         #     self.i_mgr.Implies(self._in_loop,
         #                        symb_to_next(self.i_mgr, self._in_loop)))

        # monitors and symbols agree on truth assignment of all lback_atms
        self.bad = [self.i_mgr.Iff(subst(atm, self.symb2monitor), atm)
                    for atm in lback_atms]
        self.bad.append(fair)
        self.bad.append(self._in_loop)

        # learn ranking functions provided with the hints.
        if hints is not None:
            self._add_ranking_funs([loc.rf for h in hints for loc in h.locs
                                    if loc.rf is not None])

    def _fresh_symb(self, base: str, m_type=types.BOOL) -> FNode:
        return new_symb(self.i_mgr, base, m_type)

    def add_ranking_funs(self, ranks: List[RankFun]) -> None:
        assert isinstance(ranks, list)
        assert all(isinstance(rank, RankFun) for rank in ranks)
        assert all(rank.env == self.o_env for rank in ranks)
        self._add_ranking_funs([rank.to_env(self.i_env) for rank in ranks])

    def add_ranking_fun(self, rank: RankFun) -> None:
        assert isinstance(rank, RankFun)
        assert rank.env == self.o_env
        self._add_ranking_funs([rank.to_env(self.i_env)])

    def _add_ranking_funs(self, ranks: List[RankFun]) -> None:
        assert isinstance(ranks, list)
        assert all(isinstance(rank, RankFun) for rank in ranks)
        assert all(rank.env == self.i_env for rank in ranks)
        # self.rank_funs.extend(ranks)
        self._new_rank_fun = True
        self.bad.extend(self.cn(self.i_mgr.Not(
            to_curr(self.i_mgr,
                    self.i_env.substituter.substitute(self.i_norm(r.progress_pred()),
                                                      self.symb2monitor),
                    self.all_symbs)))
                        for r in ranks)

    def gen_loops(self) -> Iterator[
            Tuple[Optional[list],
                  Optional[int],
                  Union[Optional[Tuple[List[FrozenSet[FNode]],
                                       List[FrozenSet[FNode]]]],
                        bool],
                  Union[Optional[Tuple[List[Hint],
                                       List[FrozenSet[FNode]],
                                       List[FrozenSet[FNode]]]],
                        bool]]]:
        assert all(pred in self.i_mgr.formulae.values() for pred in self.init)
        assert all(t in self.i_mgr.formulae.values() for t in self.trans)
        # assert self.fair in self.i_mgr.formulae.values()
        assert all(b in self.i_mgr.formulae.values() for b in self.bad)
        serialize = self.i_env.serializer.serialize
        with MultiSolver(self.i_env, BMC.get_timeout(),
                         pref_vars=self.hint_active
                         if BMC.get_hints_mode() is HintMode.MAY else None,
                         log_lvl=BMC._LOG_LVL) as solver:
            timed_symbs = [frozenset(self.totime(s, 0)
                                     for s in chain(self.orig_symbs,
                                                    self.hint_symbs))]
            for pred in self.init:
                solver.add_assertion(self.totime(pred, 0))

            # BMC steps.
            for k in count(start=0, step=1):  # BMC steps.
                if BMC.get_max_k() > 0 and k > BMC.get_max_k():
                    return

                assert len(timed_symbs) == k + 1, (len(timed_symbs), k)
                timed_symbs.append(frozenset(self.totime(s, k + 1)
                                             for s in chain(self.orig_symbs,
                                                            self.hint_symbs)))
                # trans from k to k + 1
                for t in self.trans:
                    solver.add_assertion(self.totime(t, k))
                solver.push()

                for pred in self.bad:
                    solver.add_assertion(self.totime(pred, k + 1))
                self._new_rank_fun = False

                ref = None
                sat: Optional[bool] = True
                refinements: List[FNode] = []
                # enumerate loops in paths of length k + 2
                while sat:
                    log(f"\tBMC k = {k + 2}"
                        f' refinement = {"; ".join(serialize(r) for r in refinements)}',
                        BMC._LOG_LVL)
                    if self._new_rank_fun:
                        solver.pop()  # remove previous bad and refinements
                        solver.push()
                        for pred in self.bad:
                            solver.add_assertion(self.totime(pred, k + 1))
                        solver.add_assertions(refinements)  # re-add refinements.
                        self._new_rank_fun = False
                    try:
                        sat = solver.solve()
                    except SolverReturnedUnknownResultError:
                        sat = None
                        log("\tBMC timeout\n", BMC._LOG_LVL)
                        solver.reset_assertions()
                        # re-add path assertions
                        for pred in self.init:
                            solver.add_assertion(self.totime(pred, 0))
                        for it_k in range(k + 1):
                            for t in self.trans:
                                solver.add_assertion(self.totime(t, it_k))
                        solver.push()

                    if sat is None:
                        # notify that we might have skipped some path.
                        yield None, None, None, None
                    elif sat is True:
                        model = solver.get_model()

                        lback_idx = self._get_lback_index(model, k + 1)
                        assert isinstance(lback_idx, int)
                        assert lback_idx >= 0
                        assert lback_idx < k + 1

                        loop_core: Optional[FrozenSet[FNode]] = None
                        hints_region_trans, hints_assume = None, None

                        try:
                            conc_model = self._try_concretize(solver, k + 1,
                                                              lback_idx)
                        except SolverReturnedUnknownResultError:
                            conc_model = None
                            log("\tBMC try-concretize timeout\n", BMC._LOG_LVL)
                            solver.reset_assertions()
                            # re-add path assertions
                            for pred in self.init:
                                solver.add_assertion(self.totime(pred, 0))
                            for it_k in range(k + 1):
                                for t in self.trans:
                                    solver.add_assertion(self.totime(t, it_k))
                            solver.push()

                        if conc_model is not None:
                            trace = self._model2trace(conc_model, 0, k + 1,
                                                      True)
                            yield (trace, lback_idx, False, False)
                        else:
                            hint_comp = \
                                self._model2hint_comp(model,
                                                      lback_idx, k + 1)
                            assert len(hint_comp) == 2
                            assert len(hint_comp[0]) == 0 or \
                                len(hint_comp[1]) == k - lback_idx + 1
                            hints_region_trans, hints_assume = \
                                self._hint_comp2assume(hint_comp, lback_idx)
                            assert isinstance(hints_region_trans, dict)
                            assert all(isinstance(k, FNode)
                                       for k in hints_region_trans)
                            assert all(isinstance(v, FNode)
                                       for v in hints_region_trans.values())
                            assert all(k in self.i_mgr.formulae.values()
                                       for k in hints_region_trans)
                            assert all(v in self.i_mgr.formulae.values()
                                       for v in hints_region_trans.values())
                            assert all(v.is_true() or v.is_false()
                                       for v in hints_region_trans.values())
                            assert isinstance(hints_assume, dict)
                            assert all(isinstance(k, FNode)
                                       for k in hints_assume)
                            assert all(isinstance(v, FNode)
                                       for v in hints_assume.values())
                            assert all(k in self.i_mgr.formulae.values()
                                       for k in hints_assume)
                            assert all(v in self.i_mgr.formulae.values()
                                       for v in hints_assume.values())
                            assert all(v.is_true() or v.is_false()
                                       for v in hints_assume.values())

                            hint_symbs_assign = {k: model.get_value(k)
                                                 for k in self.hint_active}
                            for step in range(lback_idx, k+2):
                                for s in self.hint_symbs:
                                    timed_s = self.totime(s, step)
                                    hint_symbs_assign[timed_s] = model.get_value(timed_s)
                            loop_core = self.generaliser.generalise_path(
                                chain(solver.assertions,
                                      (k if v.is_true() else self.i_mgr.Not(k)
                                       for k, v in hints_assume.items())),
                                model,
                                timed_symbs[lback_idx:],
                                lback_idx, k + 1,
                                assume={**hints_region_trans,
                                        **hint_symbs_assign})
                            assert isinstance(loop_core, frozenset)
                            assert all(c in self.i_mgr.formulae.values()
                                       for c in loop_core)
                            if __debug__:
                                from solver import Solver
                                # loop_core -> original trans
                                _trans = [self.totime(self._orig_trans, _time)
                                          for _time in range(lback_idx, k + 1)]
                                _trans = self.i_mgr.And(_trans)
                                with Solver(self.i_env) as _solver:
                                    _solver.add_assertion(self.i_mgr.Not(_trans))
                                    for c in loop_core:
                                        _solver.add_assertion(c)
                                    for pred in assign2fnodes(self.i_env,
                                                              hint_symbs_assign,
                                                              hints_region_trans):
                                        _solver.add_assertion(pred)
                                    sat = _solver.solve()
                                    assert sat is False

                            abst_states, abst_trans = \
                                self.generaliser.curr_next_preds(
                                    loop_core, lback_idx, k + 1, model)
                            hints_states, hints_trans = \
                                self.generaliser.curr_next_preds(
                                    frozenset(
                                        k if v.is_true() else self.i_mgr.Not(k)
                                        for k, v in hints_region_trans.items()),
                                    lback_idx, k + 1, model)

                            abst_states = \
                                [frozenset(self.o_norm(s)
                                           for s in state)
                                 for state in abst_states]
                            abst_trans = \
                                [frozenset(self.o_norm(t)
                                           for t in trans)
                                 for trans in abst_trans]
                            hints_states = \
                                [frozenset(self.o_norm(s)
                                           for s in state)
                                 for state in hints_states]
                            hints_trans = \
                                [frozenset(self.o_norm(t)
                                           for t in trans)
                                 for trans in hints_trans]

                            trace = self._model2trace(model, 0, k + 1,
                                                      True)
                            assert isinstance(trace, list), trace
                            assert len(trace) == k + 2
                            assert isinstance(abst_states, list)
                            assert isinstance(abst_trans, list)
                            assert len(abst_states) == \
                                len(trace) - lback_idx
                            assert len(abst_trans) == len(abst_states) - 1
                            assert isinstance(hints_states, list)
                            assert isinstance(hints_trans, list)
                            assert len(hints_states) == \
                                len(trace) - lback_idx
                            assert len(hints_trans) == len(hints_states) - 1

                            yield (trace, lback_idx,
                                   (abst_states, abst_trans),
                                   ([h.to_env(self.o_env)
                                     for h in hint_comp[0]],
                                    hints_states, hints_trans))
                            del trace

                        ref = self._compute_refinement(model, lback_idx, k + 1,
                                                       hints_region_trans,
                                                       hints_assume,
                                                       loop_core)
                        refinements.append(ref)
                        solver.add_assertion(ref)
                solver.pop()

    def _try_concretize(self, solver, last: int, lback: int):
        assert isinstance(last, int)
        assert last >= 0
        assert isinstance(lback, int)
        assert lback >= 0
        assert lback < last
        assert all(s in self.i_mgr.formulae.values() for s in self.all_symbs)
        model = None
        solver.push()
        # ignore additional symbols introduced by Hints.
        for s in self.orig_symbs:
            last_s = self.totime(s, last)
            lback_s = self.totime(s, lback)
            if s.symbol_type().is_bool_type():
                solver.add_assertion(self.i_mgr.Iff(last_s, lback_s))
            else:
                solver.add_assertion(self.i_mgr.Equals(last_s, lback_s))
        if solver.solve() is True:
            model = solver.get_model()
        solver.pop()
        return model

    def _get_lback_index(self, model, last) -> int:
        """Search for lback index
        self._in_loop becomes true in the second state of the loop
        """
        assert last > 0
        # last state cannot be loop-back.
        assert model.get_value(self.totime(self._in_loop, last)).is_true()
        assert model.get_value(self.totime(self._in_loop, 0)).is_false()
        idx = last - 1
        while model.get_value(self.totime(self._in_loop, idx)).is_true():
            idx -= 1
        assert idx >= 0
        assert model.get_value(self.totime(self._in_loop, idx + 1)).is_true()
        assert model.get_value(self.totime(self._in_loop, idx)).is_false()
        assert model.get_value(self.totime(self.start_loop, idx)).is_true()
        return idx

    def _model2trace(self, model, first: int, last: int,
                     to_out: bool = False) -> List[Dict[FNode, FNode]]:
        assert isinstance(first, int)
        assert isinstance(last, int)
        assert 0 <= first < last, (first, last)
        trace: List[Dict[FNode, FNode]] = [{} for _ in range(first, last + 1)]
        for c_time in range(first, last + 1):
            idx = c_time - first
            for s in self.orig_symbs if to_out else self.all_symbs:
                timed_s = self.totime(s, c_time)
                v = model.get_value(timed_s)
                if to_out:
                    s = self.o_norm(s)
                    v = self.o_norm(v)
                assert s not in trace[idx], str(s)
                trace[idx][s] = v
        return trace

    def _model2hint_comp(self, model, first: int, last: int) \
            -> Tuple[List[Hint],
                     List[List[Tuple[int, bool, TransType]]]]:
        """returns list of active Hints and sequence of `states`.
         For each state reports location of each active hint and type of
        the transition to reach the following state"""
        assert isinstance(first, int)
        assert isinstance(last, int)
        assert hasattr(model, "get_value")
        assert 0 <= first < last
        assert all(h.ts_lvals is not None for h in self.hints)
        assert all(h.ts_loc_symbs is not None for h in self.hints)

        # set of active hints should be constant in the loop.
        assert all(all(model.get_value(self.totime(is_active, step)).is_true()
                       for step in range(first, last+1)) or
                   all(model.get_value(self.totime(is_active, step)).is_false()
                       for step in range(first, last+1))
                   for idx, is_active in enumerate(self.hint_active))
        # hint_active predicates should be frozen.
        assert all(self.totime(act, first) == act for act in self.hint_active)
        # Filter active hints
        active_hints = [self.hints[idx]
                        for idx, is_active in enumerate(self.hint_active)
                        if model.get_value(is_active).is_true()]

        # No hints used in the current trace.
        if len(active_hints) == 0:
            return [], []

        locval2idx_lst = [{val: idx
                           for idx, val in enumerate(h.ts_lvals)}
                          for h in active_hints]

        x_loc_idxs: List[int] = []
        for h, locval2idx in zip(active_hints, locval2idx_lst):
            val = self.i_mgr.And(
                s if model.get_value(self.totime(s, first)).is_true() else
                self.i_mgr.Not(s)
                    for s in h.ts_loc_symbs)
            assert val in locval2idx
            x_loc_idxs.append(locval2idx[val])

        hints_steps = [[] for _ in range(first, last)]
        for curr, step in zip(hints_steps, range(first, last)):
            # fill curr with info of active_hints
            loc_idxs = x_loc_idxs
            x_loc_idxs = []
            assert len(active_hints) == len(locval2idx_lst)
            assert len(active_hints) == len(loc_idxs)
            for h, locval2idx, loc_idx in zip(active_hints, locval2idx_lst,
                                              loc_idxs):
                # find location of h at next step
                val = self.i_mgr.And(
                    s if model.get_value(self.totime(s, step + 1)).is_true() else
                    self.i_mgr.Not(s)
                    for s in h.ts_loc_symbs)
                assert val in locval2idx
                x_loc_idx = locval2idx[val]
                assert isinstance(x_loc_idx, int)
                assert 0 <= x_loc_idx < len(h)
                x_loc_idxs.append(x_loc_idx)
                trans_type = None
                is_ranked = False
                if model.get_value(self.totime(h.t_is_stutter, step)).is_true():
                    trans_type = TransType.STUTTER
                    if h[loc_idx].rf is not None:
                        rf_pred = self.totime(h[loc_idx].rf.is_ranked, step)
                        is_ranked = model.get_value(rf_pred).is_true()
                elif model.get_value(self.totime(h.t_is_ranked, step)).is_true():
                    trans_type = TransType.RANKED
                    is_ranked = True
                else:
                    assert model.get_value(self.totime(h.t_is_progress, step)).is_true()
                    trans_type = TransType.PROGRESS

                curr.append((loc_idx, is_ranked, trans_type))
                if __debug__:
                    assert step < last
                    # check model is in the identified restricted region.
                    formula = self.totime(h[loc_idx].region, step)
                    assert model.get_value(formula).is_true()
                    formula = self.totime(h[loc_idx].assume, step)
                    assert model.get_value(formula).is_true()
                    formula = self.totime(h[x_loc_idx].region, step + 1)
                    assert model.get_value(formula).is_true()
                    formula = self.totime(h[x_loc_idx].assume, step + 1)
                    assert model.get_value(formula).is_true()
                    # check that the identified transition holds in model.
                    if trans_type == TransType.STUTTER:
                        assert x_loc_idx == loc_idx
                        trans = h[loc_idx].stutterT
                        formula = self.totime(trans, step)
                        assert model.get_value(formula).is_true()

                        if h[loc_idx].rf is not None:
                            rf = h[loc_idx].rf.expr
                            formula = self.i_mgr.Equals(self.totime(rf, step),
                                                        self.totime(rf, step + 1))
                            assert model.get_value(formula).is_true()
                    elif trans_type == TransType.RANKED:
                        assert h[loc_idx].rf is not None
                        assert x_loc_idx == loc_idx
                        trans = h[loc_idx].stutterT
                        formula = self.totime(trans, step)
                        assert model.get_value(formula).is_true()
                        formula = self.totime(h[loc_idx].rf.progress_pred, step)
                        assert model.get_value(formula).is_true()
                    else:
                        assert trans_type == TransType.PROGRESS
                        assert x_loc_idx in h[loc_idx].dsts
                        trans = self.totime(h[loc_idx].progress(x_loc_idx), step)
                        assert model.get_value(trans).is_true()
                        if h[x_loc_idx].rf is not None:
                            ranked = self.totime(
                                self.i_mgr.Not(h[loc_idx].rf.is_ranked),
                                step)
                            assert model.get_value(ranked).is_true()
                # end debug

        return (active_hints, hints_steps)

    def _hint_comp2assume(self, hint_comp:
                          Tuple[List[Hint],
                                List[List[Tuple[int, bool, TransType]]]],
                          first: int) -> Tuple[Dict[FNode, FNode],
                                               Dict[FNode, FNode]]:
        """Build dictionary from predicates to the corresponding truth assignment
        as prescribed by the selected hints."""
        assert isinstance(hint_comp, tuple)
        assert len(hint_comp) == 2
        assert isinstance(first, int)
        assert first >= 0

        hints, steps = hint_comp
        assert all(isinstance(h, Hint) for h in hints)
        assert all(isinstance(s, list) for s in steps)
        assert all(len(s) == len(hints) for s in steps)
        assert all(isinstance(s, tuple) for step in steps for s in step)
        assert all(len(s) == 3 for step in steps for s in step)
        assert all(isinstance(s[0], int) for step in steps for s in step)
        assert all(isinstance(s[1], bool) for step in steps for s in step)
        assert all(isinstance(s[2], TransType) for step in steps for s in step)
        if len(hints) == 0:
            return {}, {}

        def assign_true(pred: FNode, res: dict):
            assert isinstance(pred, FNode)
            preds = [pred]
            while preds:
                pred = preds.pop()
                if pred.is_and():
                    preds.extend(pred.args())
                elif pred.is_not():
                    assign_false(pred.arg(0), res)
                elif not pred.is_true():
                    assert not pred.is_false()
                    res[pred] = self.i_mgr.TRUE()

        def assign_false(pred: FNode, res: dict):
            assert isinstance(pred, FNode)
            preds = [pred]
            while preds:
                pred = preds.pop()
                if pred.is_or():
                    preds.extend(pred.args())
                elif pred.is_not():
                    assign_true(pred.arg(0), res)
                elif not pred.is_false():
                    assert not pred.is_true()
                    res[pred] = self.i_mgr.FALSE()

        res_regions_trans: Dict[FNode, FNode] = {}
        res_assumes: Dict[FNode, FNode] = {}
        for step_idx, step in enumerate(steps):
            c_time = step_idx + first
            x_step_idx = (step_idx + 1) % len(steps)
            for hint_idx, (hint, (loc_idx, is_ranked, trans_t)) in enumerate(
                    zip(hints, step)):
                assert isinstance(hint, Hint)
                assert isinstance(loc_idx, int)
                assert isinstance(trans_t, TransType)
                loc = hint[loc_idx]

                assign_true(self.totime(loc.region, c_time), res_regions_trans)
                assign_true(self.totime(loc.assume, c_time), res_assumes)
                if loc.rf is not None:
                    if is_ranked:
                        assign_true(self.totime(loc.rf.is_ranked, c_time),
                                    res_regions_trans)
                    else:
                        assign_false(self.totime(loc.rf.is_ranked, c_time),
                                     res_regions_trans)
                x_loc_idx = steps[x_step_idx][hint_idx][0]
                assert isinstance(x_loc_idx, int)
                if trans_t == TransType.PROGRESS:
                    trans = loc.progress(x_loc_idx)
                elif trans_t == TransType.STUTTER:
                    trans = loc.stutterT
                else:
                    assert trans_t == TransType.RANKED
                    trans = loc.rankT
                assert trans is not None
                assert isinstance(trans, FNode)
                assert not trans.is_false()
                assert trans in self.i_mgr.formulae.values()
                assign_true(self.totime(trans, c_time), res_regions_trans)

        return res_regions_trans, res_assumes

    def _compute_refinement(self, model,
                            lback_idx: int, last_idx: int,
                            hints_region_trans: Optional[Dict[FNode, FNode]],
                            hints_assume: Optional[Dict[FNode, FNode]],
                            loop_core: Optional[FrozenSet[FNode]]) -> FNode:
        assert hasattr(model, "get_value")
        assert isinstance(lback_idx, int)
        assert isinstance(last_idx, int)
        assert 0 <= lback_idx < last_idx
        res = set()
        if hints_region_trans:
            assert isinstance(hints_region_trans, dict)
            assert isinstance(hints_assume, dict)
            for pred, v in chain(hints_region_trans.items(),
                                 hints_assume.items()):
                assert isinstance(pred, FNode)
                assert isinstance(v, FNode)
                assert v.is_true() or v.is_false()
                if __debug__:
                    pred_times = \
                        ExprAtTime.collect_times(self.i_mgr,
                                                 pred)
                    assert 1 <= len(pred_times) <= 2, pred
                    assert max(pred_times) <= last_idx, pred
                if v.is_false():
                    assert model.get_value(pred).is_false()
                    pred = self.i_mgr.Not(pred)
                assert model.get_value(pred).is_true()
                res.add(self.cn(pred))
        else:
            for pred in self.hint_active:
                assert isinstance(pred, FNode)
                if model.get_value(pred).is_false():
                    pred = self.i_mgr.Not(pred)
                assert model.get_value(pred).is_true()
                res.add(pred)

        if loop_core:
            assert isinstance(loop_core, frozenset)
            assert all(isinstance(pred, FNode) for pred in loop_core)
            for pred in loop_core:
                pred = pred.arg(0) if pred.is_not() else pred
                assert not pred.is_not()
                assert pred == self.cn(pred)
                if __debug__:
                    _times = \
                        ExprAtTime.collect_times(self.i_mgr, pred)
                    assert 1 <= len(_times) <= 2
                    assert max(_times) <= last_idx, pred
                # skip LTL tableau symbols.
                if pred.is_symbol() and (pred.symbol_name().startswith("_J") or
                                         pred.symbol_name().startswith("_EL_")):
                    continue

                if model.get_value(pred).is_false():
                    pred = self.i_mgr.Not(pred)
                assert model.get_value(pred).is_true()
                res.add(pred)
        else:
            i_get_atoms = self.i_env.ao.get_atoms
            for idx in range(lback_idx, last_idx + 1):
                for pred in i_get_atoms(self._orig_trans):
                    assert not pred.is_not()
                    # skip LTL tableau symbols.
                    if pred.is_symbol() and (pred.symbol_name().startswith("_J") or
                                             pred.symbol_name().startswith("_EL_")):
                        continue

                    pred = self.totime(pred, idx)
                    _times = \
                        ExprAtTime.collect_times(self.i_mgr, pred)
                    assert 1 <= len(_times) <= 2, pred
                    if max(_times) <= last_idx:
                        if model.get_value(pred).is_false():
                            pred = self.i_mgr.Not(pred)
                        assert model.get_value(pred).is_true()
                        res.add(pred)
        assert all(not s.symbol_name().startswith("_J") and
                   not s.symbol_name().startswith("_EL_")
                   for pred in res
                   for s in self.i_env.fvo.get_free_variables(pred))
        return self.i_mgr.Not(self.i_mgr.And(res))
