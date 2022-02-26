from typing import FrozenSet, Set, List, Tuple, Optional, Iterable, Dict
from enum import IntEnum
from itertools import chain

from pysmt.environment import Environment as PysmtEnv
from pysmt.fnode import FNode
from pysmt.solvers.solver import Model
from pysmt.exceptions import SolverReturnedUnknownResultError

from expr_at_time import ExprAtTime
from canonize import Canonizer
from trans_system import TransSystem
from multisolver import MultiSolver
from rankfun import RankFun
from hint import Hint, TransType
from expr_utils import (new_symb, new_frozen, symb2next, symb_is_thawed,
                        symb_is_frozen, to_curr, to_next, assigns2fnodes,
                        not_rel)
from utils import log


class HintMode(IntEnum):
    MAY = 0
    MUST = 1
    ALL = 2


class BMC:
    """Iterate over loops via BMC"""

    _LOG_LVL = 1
    _TIMEOUT = 30
    _MAX_K = -1
    _HINT_MODE = HintMode.MUST
    _FAIR_LBACK = True

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

    @staticmethod
    def get_fair_lback() -> bool:
        return BMC._FAIR_LBACK

    @staticmethod
    def set_fair_lback(val: bool) -> None:
        assert isinstance(val, bool)
        BMC._FAIR_LBACK = val

    def __init__(self, ts: TransSystem, fair: FNode,
                 hints: FrozenSet[Hint]):
        assert isinstance(ts, TransSystem)
        assert isinstance(ts.env, PysmtEnv)
        assert isinstance(fair, FNode)
        assert fair in ts.env.formula_manager.formulae.values()
        assert isinstance(hints, frozenset)
        assert all(isinstance(h, Hint) for h in hints)
        assert all(h.env == ts.env for h in hints)
        assert all(h0 is h1 or h0.name != h1.name
                   for h0 in hints for h1 in hints)
        self.env = ts.env
        get_free_vars = self.env.fvo.get_free_variables
        get_atoms = self.env.ao.get_atoms
        subst = self.env.substituter.substitute
        mgr = self.env.formula_manager
        self.totime = ExprAtTime(self.env)
        self.cn = Canonizer(self.env)
        self.td = self.cn.td
        self.orig_ts = ts
        self.hints = sorted(hints, key=lambda h: h.name)

        self.fair_symbs = frozenset(s for s in self.orig_ts.symbs
                                    if s.symbol_name().startswith("_J"))
        assert all(s.symbol_type().is_bool_type() for s in self.fair_symbs)
        self.symbs = (self.orig_ts.symbs |
                      frozenset(chain.from_iterable(h.all_symbs
                                                    for h in self.hints)))
        self.symbs -= self.fair_symbs
        assert self.symbs | self.fair_symbs >= self.orig_ts.symbs

        ts = TransSystem(self.env, ts.symbs, ts.init, ts.trans)
        self.hint_active = [new_frozen(self.env, f"{h.name}")
                            for h in self.hints]
        assert len(self.orig_ts.symbs & frozenset(self.hint_active)) == 0
        # frozen symbols should not change with time.
        assert all(symb_is_frozen(s) for s in self.hint_active)
        assert all(self.totime(s, 5) == s for s in self.hint_active)

        hints_ts = [h.get_trans_system(active)
                    for h, active in zip(self.hints, self.hint_active)]
        hint_loc_active = [loc_active for _, loc_active in hints_ts]
        hints_ts = [ts for ts, _ in hints_ts]
        assert all(isinstance(p, FNode) for p in hint_loc_active)
        assert all(isinstance(h, TransSystem) for h in hints_ts)

        ts.prods(hints_ts)
        assert fair in mgr.formulae.values()
        assert all(s in mgr.get_all_symbols()
                   for s in get_free_vars(fair))
        assert all(s in mgr.get_all_symbols()
                   for s in self.orig_ts.symbs)
        assert get_free_vars(fair) <= self.orig_ts.symbs
        assert len(self.fair_symbs) == 0 or \
            get_free_vars(fair) <= self.fair_symbs

        thawed_symbs = frozenset(s for s in self.symbs
                                 if symb_is_thawed(s))
        assert len(thawed_symbs & self.fair_symbs) == 0
        # collect atoms for abstract loop-back detection.
        lback_atms = set()
        for pred in chain((p for p in get_atoms(fair)
                           if get_free_vars(p) & thawed_symbs),
                          (p for c_init in ts.init
                           for p in get_atoms(c_init)
                           if get_free_vars(p) & thawed_symbs)):
            assert get_free_vars(pred) & thawed_symbs
            lback_atms.add(pred)
            if pred.is_equals():
                lback_atms.add(mgr.LT(pred.arg(0), pred.arg(1)))
        # cx_fair_symbs = self.fair_symbs | frozenset(symb2next(self.env, s)
        #                                             for s in self.fair_symbs)
        cx_thawed_symbs = thawed_symbs | frozenset(symb2next(self.env, s)
                                                   for s in thawed_symbs)
        # TODO: consider also curr-next preds, may prune some extra states.
        for pred in frozenset(chain.from_iterable(get_atoms(tr)
                                                  for tr in ts.trans)):
            free_v = get_free_vars(pred)
            if all(s not in cx_thawed_symbs for s in free_v):
                continue
            # if free_v & cx_fair_symbs:
            #     assert free_v <= cx_fair_symbs
            #     continue
            assert free_v <= self.symbs | frozenset(symb2next(self.env, s)
                                                    for s in self.symbs)
            intsec_size = len(free_v & thawed_symbs)
            # either all current or all next.
            if intsec_size == len(free_v) or intsec_size == 0:
                if intsec_size == 0:
                    pred = to_curr(self.env, pred, self.symbs)
                lback_atms.add(pred)
                if pred.is_equals():
                    lback_atms.add(mgr.LT(pred.arg(0), pred.arg(1)))
        assert all(get_free_vars(s) <= self.symbs
                   for s in lback_atms)
        assert all(a.is_theory_relation() or
                   (a.is_symbol() and a.symbol_type().is_bool_type())
                   for a in lback_atms)

        if self.hints:
            # active Hints must have disjoint symbols.
            ts.ext_init(Hint.disjoint_symbs(self.env, self.hints,
                                            self.hint_active))
            # invariant: minimise 1 ranking function at a time.
            at_most_1_ranked = list(Hint.at_most_1_ranked(self.env, self.hints,
                                                          self.hint_active))
            ts.ext_init(at_most_1_ranked)
            ts.ext_trans(to_next(self.env, pred, self.symbs)
                         for pred in at_most_1_ranked)
            # add constraint corresponding to hint encoding mode.
            if BMC.get_hints_mode() is HintMode.MUST:
                ts.add_init(mgr.Or(self.hint_active))
            elif BMC.get_hints_mode() is HintMode.ALL:
                ts.ext_init(self.hint_active)
            else:
                assert BMC.get_hints_mode() is HintMode.MAY

        self.symb2monitor = \
            {s: new_frozen(self.env, f"{s.symbol_name()}", s.symbol_type())
             for s in self.symbs | self.fair_symbs}

        self._in_loop = new_symb(self.env, "inloop")
        ts.add_symb(self._in_loop)
        ts.add_init(mgr.Not(self._in_loop))
        # loop begins if all(symb == monitor) & all(h_active -> h_loc_active)
        start_loop = mgr.And(
            chain(assigns2fnodes(self.env, self.symb2monitor),
                  (mgr.Implies(h_act, h_loc_act)
                   for h_act, h_loc_act in zip(self.hint_active,
                                               hint_loc_active)),
                  # all true or all false.
                  [mgr.And(self.fair_symbs) if BMC.get_fair_lback()
                   else mgr.Or(mgr.And(self.fair_symbs),
                               mgr.And(mgr.Not(s) for s in self.fair_symbs))]
                  if self.fair_symbs else []))
        # inloop' -> inloop | start.
        x_in_loop = symb2next(self.env, self._in_loop)
        ts.add_trans(mgr.Or(mgr.Not(x_in_loop),
                            self._in_loop, start_loop))
        # inloop -> inloop'
        ts.add_trans(mgr.Implies(self._in_loop, x_in_loop))

        self.ts = ts

        # monitors and symbols agree on truth assignment of all lback_atms
        self._bad = set(mgr.Iff(subst(atm, self.symb2monitor), atm)
                        for atm in lback_atms)
        assert all(h.trans_type_symbs is not None for h in self.hints)
        self.enc_symbs = frozenset(chain(self.symb2monitor.values(),
                                         self.hint_active, [self._in_loop],
                                         chain.from_iterable(h.trans_type_symbs
                                                             for h in self.hints),
                                         (h.is_rank_decr for h in self.hints
                                          if not h.is_rank_decr.is_false())))
        assert all(s in mgr.get_all_symbols() for s in self.enc_symbs)
        self._bad.add(fair)
        self._bad.add(self._in_loop)
        self.last_k = 0
        self.k = 1
        self._n_visited: List[List[FNode]] = []
        self.solver = MultiSolver(self.env, BMC.get_timeout(),
                                  pref_vars=self.hint_active
                                  if BMC.get_hints_mode() is HintMode.MAY
                                  else None,
                                  log_lvl=BMC._LOG_LVL)
        self.solver.add_assertions(self.totime(pred, 0)
                                   for pred in chain(self.ts.init,
                                                     self.ts.trans))
        self.solver.push()
        self._assert_not_visited()
        self._assert_bad()
        if __debug__:
            all_symbs = self.symbs | self.enc_symbs | self.fair_symbs
            for h in self.hints:
                assert h.ts_loc_symbs is not None
                assert h.trans_type_symbs is not None
                all_symbs |= frozenset(h.ts_loc_symbs)
                all_symbs |= frozenset(h.trans_type_symbs)
            all_symbs |= frozenset(symb2next(self.env, s) for s in all_symbs)
            assert all(get_free_vars(pred) <= all_symbs for pred in ts.trans)

    def next(self) -> Optional[Tuple[bool, Model, int]]:
        """Returns triple <lasso_symbs, trace, lback_time>.
        lasso_symbs is the subset of symbols describing a concrete lasso,
        where lback_time is the lback state idx.

        Returns None if unable to decide whether a path of length `k` exists.
        Caller should add refinements between calls to `next` to avoid
        generating the same result.
        """
        log(f"\tBMC k = {self.k}", BMC._LOG_LVL)
        try:
            sat = self.solver.solve()
        except SolverReturnedUnknownResultError:
            log("\tBMC timeout\n", BMC._LOG_LVL)
            # re-add path assertions
            self._reset_assertions()
            # notify that we might have skipped some path.
            return None
        assert sat in {True, False}
        while sat is False:
            # if __debug__:
            #     from solver import UnsatCoreSolver
            #     serialize = self.env.serializer.serialize
            #     with UnsatCoreSolver(self.env,
            #                          unsat_cores_mode="named") as _solver:
            #         for i, p in enumerate(self.solver.assertions):
            #             _solver.add_assertion(p, named=f"n{i}")
            #         _sat = _solver.solve()
            #         assert _sat is False
            #         cores = _solver.get_named_unsat_core()
            #         for k, p in cores.items():
            #             print(f"{k} : {serialize(p)}")
            # BMC unrolling: add another step.
            self.step()
            log(f"\tBMC k = {self.k}", BMC._LOG_LVL)
            try:
                sat = self.solver.solve()
            except SolverReturnedUnknownResultError:
                log("\tBMC timeout\n", BMC._LOG_LVL)
                # re-add path assertions
                self._reset_assertions()
                # notify that we might have skipped some path.
                return None

        model = self.solver.get_model()
        is_lasso = False
        if self.last_k < self.k:
            self.last_k = self.k
            if __debug__:
                dbg_asserts = frozenset(self.solver.assertions)
            _model = self._concretize_loop()
            assert dbg_asserts == frozenset(self.solver.assertions)
            if _model is not None:
                model = _model
                is_lasso = True
        return is_lasso, model, self._lback_time(model)

    def step(self) -> None:
        # remove bad and not_visited.
        self.solver.pop()
        # add step.
        self.solver.add_assertions(self.totime(pred, self.k)
                                   for pred in self.ts.trans)
        self.solver.push()
        self.k += 1
        # generate only fresh loops.
        self._assert_not_visited()
        # loop must be fair.
        self._assert_bad()

    def refine_rf(self, rf: RankFun) -> None:
        assert isinstance(rf, RankFun)
        assert rf.env == self.env
        mgr = self.env.formula_manager
        subst = self.env.substituter.substitute
        # ranking function cannot decrease in loop.
        p = self.cn(mgr.Not(
            to_curr(self.env,
                    subst(mgr.And(rf.is_ranked(), rf.is_decr()),
                          self.symb2monitor), self.symbs)))
        assert not p.is_bool_constant()
        self._bad.add(p)
        self.solver.add_assertion(self.totime(p, self.k))

    def refine_rfs(self, rfs: Iterable[RankFun]) -> None:
        mgr = self.env.formula_manager
        subst = self.env.substituter.substitute
        # ranking functions cannot decrease in loop.
        preds = frozenset(self.cn(mgr.Not(to_curr(
            self.env, subst(mgr.And(rf.is_ranked(), rf.is_decr()),
                            self.symb2monitor), self.symbs)))
                          for rf in rfs)
        self._bad.update(preds)
        self.solver.add_assertions(self.totime(p, self.k)
                                   for p in preds)

    def _add_n_visited(self, preds: List[FNode]):
        """Add predicates that must hold in non-visited candidates.
        Each element of the list prescribes conditions on different consecutive
        steps. Steps are disjunctive."""
        assert isinstance(preds, list)
        assert len(preds) >= 1
        assert len(preds) <= self.k
        assert all(isinstance(p, FNode) for p in preds)
        assert all(p in self.env.formula_manager.formulae.values()
                   for p in preds)
        self._n_visited.append(preds)
        self._assert_not_visited(start_idx=-1)

    def refine_loop(self, steps: List[Iterable[FNode]],
                    conds: Optional[List[Optional[FNode]]] = None) -> None:
        """Refine candidate loops such that: steps -> \/ conds.
        If `conds` is None avoid generating steps again: !steps,
        otherwise, allow steps only if one of conds holds."""
        assert isinstance(steps, list)
        assert len(steps) >= 1
        assert len(steps) <= self.k
        assert conds is None or isinstance(conds, list)
        assert conds is None or len(conds) == len(steps)
        assert conds is None or all(p is None or isinstance(p, FNode)
                                    for p in conds)
        assert conds is None or all(p is None or
                                    p in self.env.formula_manager.formulae.values()
                                    for p in conds)
        mgr = self.env.formula_manager
        # in_loop | conds[0] | !steps[0]
        pred = self._in_loop
        if conds is not None and conds[0] is not None:
            pred = mgr.Or(pred, conds[0])
        preds = [mgr.Or(pred, mgr.Or(mgr.Not(p) for p in steps[0]))]
        # n_in_loop = mgr.Not(self._in_loop)
        # for idx, step in enumerate(steps[1:], start=1):
        #     pred = n_in_loop
        #     if conds is not None and conds[idx] is not None:
        #         pred = mgr.Or(pred, conds[idx])
        #     # ! in_loop | conds[idx] | !steps[idx]
        #     preds.append(mgr.Or(pred, mgr.Or(mgr.Not(p) for p in steps[idx])))
        if len(steps) > 1:
            # !in_loop | conds[1] | !steps[1]
            pred = mgr.Not(self._in_loop)
            if conds is not None and conds[1] is not None:
                pred = mgr.Or(pred, conds[1])
            preds.append(mgr.Or(pred, mgr.Or(mgr.Not(p) for p in steps[1])))
            # conds[i] | !steps[i]
            for idx, step in enumerate(steps[2:], start=2):
                pred = mgr.Or(mgr.Not(p) for p in step)
                if conds is not None and conds[idx] is not None:
                    pred = mgr.Or(pred, conds[idx])
                preds.append(pred)
        assert len(preds) == len(steps)
        self._add_n_visited(preds)

    def remove_loop_tmp(self, steps: List[Iterable[FNode]]) -> None:
        """Do not generate candidate loop described by `steps` until
        path length is increased"""
        assert isinstance(steps, list)
        assert len(steps) >= 1
        assert len(steps) <= self.k
        mgr = self.env.formula_manager
        # in_loop | !steps[0]
        preds = [mgr.Or(self._in_loop, mgr.Or(mgr.Not(p) for p in steps[0]))]
        if len(steps) > 1:
            # !in_loop | !steps[1]
            preds.append(mgr.Or(mgr.Not(self._in_loop),
                                mgr.Or(mgr.Not(p) for p in steps[1])))
            # !steps[i]
            preds.extend(mgr.Or(mgr.Not(p) for p in step)
                         for step in steps[2:])
        assert len(preds) == len(steps)
        self.solver.add_assertion(
            mgr.Or(self.totime(p, self.k - idx)
                   for idx, p in enumerate(reversed(preds), start=1)))

    def hints_comp(self, model: Model, start: int, end: int) -> \
        Tuple[FrozenSet[FNode], List[Set[FNode]],
              List[Set[FNode]], List[Set[FNode]],
              Dict[Tuple[int, int], RankFun]]:
        """Return: set of symbols owned by hints, list of regions,
                    list of assumptions, list of transitions,
                    list of <ranking functions, start_idx, end_idx>;
        described by model from `start` to `end`"""
        assert hasattr(model, "get_value")
        assert isinstance(start, int)
        assert isinstance(end, int)
        assert 0 <= start < end <= self.k
        hints, steps, rfs = self._hint_steps(model, self.hints, start, end)
        assert len(steps) == end - start
        regions, assumes, trans = self._hint_steps2regions(model, hints, start,
                                                           steps)
        assert len(steps) == len(regions)
        assert len(regions) == len(assumes)
        assert len(regions) == len(trans)
        return (frozenset(chain.from_iterable(h.owned_symbs for h in hints)),
                regions, assumes, trans, rfs)

    def _concretize_loop(self) -> Optional[Model]:
        self.solver.push()
        assert frozenset(self.symb2monitor.keys()) <= self.orig_ts.symbs
        self.solver.add_assertions(assigns2fnodes(
            self.env,
            {self.totime(s, self.k): self.symb2monitor[s]
             for s in self.orig_ts.symbs}))
        try:
            sat = self.solver.solve()
        except SolverReturnedUnknownResultError:
            log("\tLoop-concretize timeout\n", BMC._LOG_LVL)
            self._reset_assertions()
            return None
        if sat is False:
            self.solver.pop()
            return None
        model = self.solver.get_model()
        self.solver.pop()
        return model

    def _lback_time(self, model: Model) -> int:
        """Get loop-back time of current trace"""
        assert hasattr(model, "get_value")
        assert self.k > 0
        # last state cannot be loop-back.
        assert model.get_value(self.totime(self._in_loop,
                                           self.k)).is_true()
        assert model.get_value(self.totime(self._in_loop, 0)).is_false()
        idx = self.k - 1
        while model.get_value(self.totime(self._in_loop, idx)).is_true():
            idx -= 1
        assert idx >= 0
        assert model.get_value(self.totime(self._in_loop,
                                           idx + 1)).is_true()
        assert model.get_value(self.totime(self._in_loop, idx)).is_false()
        return idx

    def _assert_not_visited(self, start_idx: int = 0) -> None:
        mgr = self.env.formula_manager
        self.solver.add_assertions(
            mgr.Or(self.totime(p, self.k - idx)
                   for idx, p in enumerate(reversed(preds), start=1))
            for preds in self._n_visited[start_idx:])

    def _assert_bad(self) -> None:
        self.solver.add_assertions(self.totime(pred, self.k)
                                   for pred in self._bad)

    def _reset_assertions(self) -> None:
        self.solver.reset_assertions()
        self.solver.add_assertions(self.totime(pred, 0)
                                   for pred in self.ts.init)
        for step in range(self.k):
            self.solver.add_assertions(self.totime(pred, step)
                                       for pred in self.ts.trans)
        self.solver.push()
        self._assert_not_visited()
        self._assert_bad()

    def _hint_steps(self, model: Model, hints: List[Hint],
                    first: int, last: int) -> \
        Tuple[List[Hint], List[List[Tuple[int, bool, TransType]]],
              Dict[Tuple[int, int], RankFun]]:
        """returns sequence of active hints and their `states`.
         For each state reports location of each active hint and type of
        the transition to reach the following state"""
        assert hasattr(model, "get_value")
        assert isinstance(hints, list)
        assert all(isinstance(h, Hint) for h in hints)
        assert all(h.env == self.env for h in hints)
        assert all(h.ts_lvals is not None for h in self.hints)
        assert all(h.ts_loc_symbs is not None for h in self.hints)
        assert isinstance(first, int)
        assert isinstance(last, int)
        assert 0 <= first < last
        # set of active hints should be constant in the loop.
        assert all(all(model.get_value(self.totime(is_active, step)).is_true()
                       for step in range(first, last+1)) or
                   all(model.get_value(self.totime(is_active, step)).is_false()
                       for step in range(first, last+1))
                   for idx, is_active in enumerate(self.hint_active))
        # hint_active predicates should be frozen.
        assert all(self.totime(act, first) == act for act in self.hint_active)
        hints = [self.hints[idx]
                 for idx, is_active in enumerate(self.hint_active)
                 if model.get_value(is_active).is_true()]
        hints_steps = [[] for _ in range(first, last)]
        hints_rfs: Dict[Tuple[int, int], RankFun] = {}
        if len(hints) == 0:
            return hints, hints_steps, hints_rfs

        mgr = self.env.formula_manager
        locval2idx_lst = [{val: idx for idx, val in enumerate(h.ts_lvals)}
                          for h in hints]

        x_loc_idxs: List[int] = []
        for h, locval2idx in zip(hints, locval2idx_lst):
            val = mgr.And(
                s if model.get_value(self.totime(s, first)).is_true()
                else mgr.Not(s)
                for s in h.ts_loc_symbs)
            assert val in locval2idx
            x_loc_idxs.append(locval2idx[val])

        last_rf = None
        last_rf_start_idx = None
        for curr, step in zip(hints_steps, range(first, last)):
            # fill curr with info of active_hints
            loc_idxs = x_loc_idxs
            x_loc_idxs = []
            assert len(hints) == len(locval2idx_lst)
            assert len(hints) == len(loc_idxs)
            for h, locval2idx, loc_idx in zip(hints, locval2idx_lst, loc_idxs):
                # find location of h at next step
                val = mgr.And(
                    s if model.get_value(self.totime(s, step + 1)).is_true()
                    else mgr.Not(s)
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
                        rf_pred = self.totime(h[loc_idx].rf.is_ranked(), step)
                        is_ranked = model.get_value(rf_pred).is_true()
                elif model.get_value(self.totime(h.t_is_ranked, step)).is_true():
                    trans_type = TransType.RANKED
                    is_ranked = True
                    rf = h[loc_idx].rf
                    assert rf is not None
                    if model.get_value(self.totime(rf.is_min(),
                                                   step + 1)).is_true():
                        if not last_rf:
                            assert last_rf_start_idx is None
                            last_rf = rf
                            last_rf_start_idx = step - first
                        assert last_rf is not None
                        assert last_rf_start_idx is not None
                        assert 0 <= last_rf_start_idx <= step - first
                        assert (last_rf_start_idx, last_rf) not in hints_rfs
                        hints_rfs[(last_rf_start_idx, step - first)] = last_rf
                        last_rf = None
                        last_rf_start_idx = None
                    else:
                        assert last_rf is None or last_rf == rf
                        last_rf = rf
                        last_rf_start_idx = step - first + 1
                else:
                    assert model.get_value(self.totime(h.t_is_progress,
                                                       step)).is_true()
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
                            formula = self.totime(rf.is_const(), step)
                            assert model.get_value(formula).is_true()
                    elif trans_type == TransType.RANKED:
                        assert h[loc_idx].rf is not None
                        assert x_loc_idx == loc_idx
                        trans = h[loc_idx].rankT
                        formula = self.totime(trans, step)
                        assert model.get_value(formula).is_true()
                        formula = mgr.And(h[loc_idx].rf.is_ranked(),
                                          h[loc_idx].rf.is_decr())
                        formula = self.totime(formula, step)
                        assert model.get_value(formula).is_true()
                    else:
                        assert trans_type == TransType.PROGRESS
                        assert x_loc_idx in h[loc_idx].dsts
                        trans = self.totime(h[loc_idx].progress(x_loc_idx),
                                            step)
                        assert model.get_value(trans).is_true()
                        if h[x_loc_idx].rf is not None:
                            ranked = self.totime(h[loc_idx].rf.is_min(),
                                                 step)
                            assert model.get_value(ranked).is_true()
                # end debug
        return hints, hints_steps, hints_rfs

    def _hint_steps2regions(self, model: Model, hints: List[Hint],
                            first: int,
                            steps: List[List[Tuple[int, bool, TransType]]]) -> \
            Tuple[List[Set[FNode]], List[Set[FNode]],
                  List[Set[FNode]]]:
        assert hasattr(model, "get_value")
        assert isinstance(hints, list)
        assert all(isinstance(h, Hint) for h in hints)
        assert all(h.env == self.env for h in hints)
        assert isinstance(first, int)
        assert isinstance(steps, list)
        assert all(isinstance(s, list) for s in steps)
        assert all(isinstance(el, tuple) for s in steps for el in s)
        assert all(len(el) == 3 for s in steps for el in s)
        assert all(isinstance(i, int) for s in steps for i, _, _ in s)
        assert all(i >= 0 for s in steps for i, _, _ in s)
        assert all(isinstance(b, bool) for s in steps for _, b, _ in s)
        assert all(isinstance(t, TransType) for s in steps for _, _, t in s)
        regions: List[Set[FNode]] = [set() for _ in steps]
        assumes: List[Set[FNode]] = [set() for _ in steps]
        trans_l: List[Set[FNode]] = [set() for _ in steps]
        if len(hints) == 0:
            return regions, assumes, trans_l

        def assign_true(pred: FNode, res: Set[FNode]):
            assert isinstance(pred, FNode)
            assert isinstance(res, set)
            preds = [pred]
            while preds:
                pred = preds.pop()
                if pred.is_and():
                    preds.extend(pred.args())
                elif pred.is_not():
                    assign_false(pred.arg(0), res)
                elif not pred.is_true():
                    assert not pred.is_false()
                    res.add(self.cn(pred))

        def assign_false(pred: FNode, res: Set[FNode]):
            assert isinstance(pred, FNode)
            assert isinstance(res, set)
            mgr = self.env.formula_manager
            preds = [pred]
            while preds:
                pred = preds.pop()
                if pred.is_or():
                    preds.extend(pred.args())
                elif pred.is_not():
                    assign_true(pred.arg(0), res)
                elif not pred.is_false():
                    assert not pred.is_true()
                    if pred.is_lt() or pred.is_le():
                        res.add(self.cn(not_rel(self.env, pred)))
                    else:
                        res.add(self.cn(mgr.Not(pred)))

        for step_idx, (step, region, assume, trans) in enumerate(
                zip(steps, regions, assumes, trans_l)):
            x_steps = steps[(step_idx + 1) % len(steps)]
            for (hint, (loc_idx, is_ranked, trans_t),
                 (x_loc_idx, _, _)) in zip(hints, step, x_steps):
                assert isinstance(hint, Hint)
                assert isinstance(loc_idx, int)
                assert isinstance(trans_t, TransType)
                assert isinstance(x_loc_idx, int)
                loc = hint[loc_idx]

                assign_true(loc.region, region)
                assign_true(loc.assume, assume)
                if loc.rf is not None:
                    if is_ranked:
                        assign_true(loc.rf.is_ranked() if is_ranked
                                    else loc.rf.is_min(), region)
                if trans_t == TransType.PROGRESS:
                    t = loc.progress(x_loc_idx)
                elif trans_t == TransType.STUTTER:
                    t = loc.stutterT
                else:
                    assert trans_t == TransType.RANKED
                    t = loc.rankT
                assert t is not None
                assert isinstance(t, FNode)
                assert not t.is_false()
                assert t in self.env.formula_manager.formulae.values()
                assign_true(t, trans)

        assert len(regions) == len(assumes)
        assert len(regions) == len(trans_l)
        assert all(self.cn(p) == p for reg in regions for p in reg)
        assert all(self.cn(p) == p for assume in assumes for p in assume)
        assert all(self.cn(p) == p for t in trans_l for p in t)
        return regions, assumes, trans_l
