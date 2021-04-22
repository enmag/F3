from typing import Generator, Tuple, List, Optional, Union, Dict
from itertools import count
from collections.abc import Iterable

from pysmt.fnode import FNode
import pysmt.typing as types
from pysmt.environment import Environment as PysmtEnv
from pysmt.exceptions import SolverReturnedUnknownResultError

from utils import symb_to_next, to_next, to_curr, log, to_smt2
from solver import Solver, solve_with_timeout
from canonize import Canonizer
from rewritings import TimesDistributor
from expr_at_time import ExprAtTime
from generalise_path import Generaliser


class BMC:
    """Iterate over abstract loops via BMC"""

    _LOG_LVL = 2
    _PRED_MONITOR_STR = "_pred%d"
    _TIMEOUT = 20
    _MAX_K = -1
    _EXTEND_LOOP = 0

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
    def set_loop_ext_factor(val: int) -> None:
        assert val is None or isinstance(val, int)
        BMC._EXTEND_LOOP = val

    @staticmethod
    def get_loop_ext_factor() -> int:
        return BMC._EXTEND_LOOP

    def __init__(self, env: PysmtEnv, init: FNode, trans: FNode, fair: FNode,
                 all_symbs: Iterable):
        assert isinstance(env, PysmtEnv)
        assert isinstance(init, FNode)
        assert isinstance(trans, FNode)
        assert isinstance(fair, FNode)
        assert isinstance(all_symbs, Iterable)

        self.o_env = env
        self.o_mgr = env.formula_manager
        self.i_env = PysmtEnv()
        self.i_mgr = self.i_env.formula_manager
        self.totime = ExprAtTime(self.i_env,
                                 ignore_pref=BMC._PRED_MONITOR_STR[:-2])
        self.td = TimesDistributor(self.i_env)
        self.cn = Canonizer(env=self.i_env)
        self.generalise = Generaliser(self.i_env, self.cn, self.totime)
        self.all_symbs = frozenset(self.i_mgr.normalize(s)
                                   for s in all_symbs)
        init = self.i_mgr.normalize(init)
        self.orig_init = init
        trans = self.i_mgr.normalize(trans)
        self._orig_trans = trans
        self.fair = self.i_mgr.normalize(fair)
        assert self.fair.get_free_variables() <= self.all_symbs
        assert trans.get_free_variables() <= self.all_symbs | \
            frozenset(symb_to_next(self.i_mgr, s) for s in self.all_symbs)

        self.symb2monitor = {s:
                             self._fresh_symb(m_type=s.symbol_type(),
                                              base=BMC._PRED_MONITOR_STR +
                                              s.symbol_name())
                             for s in self.all_symbs}
        self.new_rank_rels = False

        # collect atoms to monitor for abstract loop-back detection.
        lback_atms = set(self.cn(a) for a in self.fair.get_atoms())
        for pred in trans.get_atoms():
            free_v = pred.get_free_variables()
            intsec_size = len(free_v & self.all_symbs)
            if intsec_size == len(free_v):
                pred = self.cn(pred)
                lback_atms.add(pred)
                if pred.is_equals():
                    lt_pred = self.cn(self.i_mgr.LT(pred.arg(0), pred.arg(1)))
                    lback_atms.add(lt_pred)
            elif intsec_size == 0:
                pred = to_curr(self.i_mgr, pred, self.all_symbs)
                pred = self.cn(pred)
                lback_atms.add(pred)
                if pred.is_equals():
                    lt_pred = self.cn(self.i_mgr.LT(pred.arg(0), pred.arg(1)))
                    lback_atms.add(lt_pred)

        lback_atms = frozenset(lback_atms)

        assert all(s.get_free_variables() <= self.all_symbs
                   for s in lback_atms)
        subst = self.i_env.substituter.substitute
        self._in_loop = self.i_mgr.Symbol("_inloop", types.BOOL)

        self.init = self.i_mgr.And(init, self.i_mgr.Not(self._in_loop))

        # loop begins if all(symb == monitor)
        self.start_loop = self.i_mgr.And(
            self.i_mgr.Iff(s, self.symb2monitor[s])
            if s.symbol_type().is_bool_type() else
            self.i_mgr.Equals(s, self.symb2monitor[s])
            for s in self.symb2monitor.keys())
        x_in_loop = symb_to_next(self.i_mgr, self._in_loop)
        t_in_loop = self.i_mgr.Or(self._in_loop, self.start_loop)
        t_in_loop = self.i_mgr.Implies(x_in_loop, t_in_loop)
        # do not canonise trans: could be large.
        self.trans = self.i_mgr.And(trans, t_in_loop)
        # lback if last assignment agrees with monitors on truth values.
        lback = self.i_mgr.And(self.i_mgr.Iff(subst(atm,
                                                    self.symb2monitor),
                                              atm)
                               for atm in lback_atms)
        lback = self.cn(self.i_mgr.And(lback, self.fair))
        self.bad = self.cn(self.i_mgr.And(self._in_loop, lback))

    def _fresh_symb(self, m_type=types.BOOL, base=_PRED_MONITOR_STR) -> FNode:
        return self.i_mgr.new_fresh_symbol(m_type, base=base)

    def add_ranking_rels(self, rels: list) -> None:
        assert isinstance(rels, list)
        assert all(isinstance(rel, FNode) for rel in rels)
        assert all(rel in self.o_mgr.formulae.values() for rel in rels)

        self.new_rank_rels = True
        subst = self.i_env.substituter.substitute
        bad = list(self.bad.args()) if self.bad.is_and() else [self.bad]
        bad.extend(self.i_mgr.Not(
            to_curr(self.i_mgr,
                    subst(self.i_mgr.normalize(rel),
                          self.symb2monitor),
                    self.all_symbs))
                   for rel in rels)
        self.bad = self.cn(self.i_mgr.And(bad))

    def add_ranking_rel(self, rel: FNode) -> None:
        assert isinstance(rel, FNode)
        assert rel in self.o_mgr.formulae.values()
        self.new_rank_rels = True
        subst = self.i_env.substituter.substitute
        bad = list(self.bad.args()) if self.bad.is_and() else [self.bad]
        bad.append(self.i_mgr.Not(to_curr(self.i_mgr,
                                          subst(self.i_mgr.normalize(rel),
                                                self.symb2monitor),
                                          self.all_symbs)))
        self.bad = self.cn(self.i_mgr.And(bad))

    def gen_loops(self) -> Generator[Tuple[Optional[list],
                                           Optional[int],
                                           Union[Optional[list], bool],
                                           Union[Optional[list], bool]],
                                     None, None]:
        assert self.init in self.i_mgr.formulae.values()
        assert self.trans in self.i_mgr.formulae.values()
        assert self.fair in self.i_mgr.formulae.values()
        assert self.bad in self.i_mgr.formulae.values()

        with Solver(env=self.i_env) as solver:
            timed_symbs = [frozenset(self.totime(s, 0)
                                     for s in self.all_symbs)]
            init0 = self.totime(self.init, 0)
            solver.add_assertion(init0)

            # BMC steps.
            for k in count(start=0, step=1):  # BMC steps.
                if BMC.get_max_k() > 0 and k > BMC.get_max_k():
                    return

                assert len(timed_symbs) == k + 1, (len(timed_symbs), k)
                timed_symbs.append(frozenset(self.totime(s, k + 1)
                                             for s in self.all_symbs))
                # trans from k to k + 1
                solver.add_assertion(self.totime(self.trans, k))
                solver.push()

                solver.add_assertion(self.totime(self.bad, k + 1))
                self.new_rank_rels = False

                ref = None
                sat: Optional[bool] = True
                refinements: List[FNode] = []
                # enumerate loops in paths of length k + 2
                while sat:
                    log("\tBMC k = {}".format(k + 2) +
                        (" refinement = {}".format(ref.serialize()) if ref
                        else ""), 1)  # BMC._LOG_LVL)
                    if self.new_rank_rels:
                        solver.pop()  # remove previous bad
                        solver.push()
                        solver.add_assertion(self.totime(self.bad, k + 1))
                        for ref in refinements:  # re-add refinements.
                            solver.add_assertion(ref)
                        self.new_rank_rels = False
                    try:
                        sat = solve_with_timeout(BMC._TIMEOUT, solver)
                    except SolverReturnedUnknownResultError:
                        sat = None
                        log("\tBMC timeout\n{}\n"
                            .format(to_smt2(solver.assertions)),
                            BMC._LOG_LVL)
                    if sat is None:
                        # notify that we might have skipped some path.
                        yield None, None, None, None
                    elif sat is True:
                        model = solver.get_model()

                        lback_idx = self._get_lback_index(model, k + 1)
                        assert isinstance(lback_idx, int)
                        assert lback_idx >= 0
                        assert lback_idx < k + 1

                        loop_core: Optional[Union[frozenset, bool]] = None
                        conc_model = self._try_concretize(solver, k + 1,
                                                          lback_idx)

                        if conc_model is not None:
                            trace = self._model2trace(conc_model, 0, k + 1,
                                                      True)
                            yield (trace, lback_idx, False, False)
                            loop_core = False
                        else:
                            loop_core = self.generalise(solver.assertions,
                                                        model,
                                                        timed_symbs[lback_idx:],
                                                        lback_idx, k + 1)
                            assert isinstance(loop_core, frozenset)
                            assert all(c in self.i_mgr.formulae.values()
                                       for c in loop_core)
                            if __debug__:
                                # loop_core -> original trans
                                _trans = [self.totime(self._orig_trans, _time)
                                          for _time in range(lback_idx, k + 1)]
                                _trans = self.i_mgr.And(_trans)
                                with Solver(env=self.i_env) as _solver:
                                    _solver.add_assertion(self.i_mgr.Not(_trans))
                                    for c in loop_core:
                                        _solver.add_assertion(c)
                                    sat = _solver.solve()
                                    assert sat is False

                            abst_states, abst_trans = \
                                self.generalise.curr_next_preds(loop_core,
                                                                lback_idx,
                                                                k + 1)
                            if BMC.get_loop_ext_factor() <= 0:
                                abst_states = \
                                    [frozenset(self.o_mgr.normalize(s)
                                               for s in state)
                                     for state in abst_states]
                                abst_trans = \
                                    [frozenset(self.o_mgr.normalize(t)
                                               for t in trans)
                                     for trans in abst_trans]

                                trace = self._model2trace(model, 0, k + 1,
                                                          True)
                                assert isinstance(trace, list), trace
                                assert len(trace) == k + 2
                                assert isinstance(abst_states, list)
                                assert isinstance(abst_trans, list)
                                assert len(abst_states) == \
                                    len(trace) - lback_idx
                                assert len(abst_trans) == len(abst_states) - 1
                                yield (trace, lback_idx, abst_states,
                                       abst_trans)
                                del trace
                            else:
                                log("\tExtend path with loop {} == {}"
                                    .format(lback_idx, k+1), BMC._LOG_LVL)
                                ext_last, ext_loop_core, ext_model = \
                                    self._extend_loop_skeleton(k + 1, model,
                                                               abst_states,
                                                               abst_trans,
                                                               BMC.get_loop_ext_factor())
                                if ext_last is not None:
                                    trace = self._model2trace(ext_model, 0,
                                                              k + 1, True)
                                    ext_trace = \
                                        self._model2trace(ext_model, k + 1,
                                                          ext_last, True)
                                    assert trace[-1] == ext_trace[0]
                                    trace.extend(ext_trace[1:])
                                    # Found a concrete loop
                                    if trace[k + 1] == trace[-1]:
                                        yield (trace, k + 1, False, False)
                                    else:
                                        abst_states, abst_trans = \
                                            self.generalise.curr_next_preds(ext_loop_core,
                                                                            k + 1,
                                                                            ext_last)
                                        abst_states = \
                                            [frozenset(self.o_mgr.normalize(s)
                                                       for s in state)
                                             for state in abst_states]
                                        abst_trans = \
                                            [frozenset(self.o_mgr.normalize(t)
                                                       for t in trans)
                                             for trans in abst_trans]
                                        del ext_last, ext_loop_core, ext_model,
                                        del ext_trace
                                        assert isinstance(trace, list), trace
                                        assert isinstance(abst_states, list)
                                        assert isinstance(abst_trans, list)
                                        assert len(abst_states) == \
                                            len(trace) - k - 1
                                        assert len(abst_trans) == \
                                            len(abst_states) - 1
                                        yield (trace, k + 1, abst_states,
                                               abst_trans)
                                        del trace
                            del abst_states, abst_trans

                        ref = []
                        if loop_core:
                            for c in loop_core:
                                assert c == self.cn(c)
                                c_times = ExprAtTime.collect_times(self.i_mgr,
                                                                   c)
                                assert 1 <= len(c_times) <= 2
                                assert max(c_times) <= k + 1, c

                                if model.get_value(c).is_true():
                                    c = self.i_mgr.Not(c)
                                else:
                                    assert model.get_value(c).is_false()
                                ref.append(c)
                        else:
                            for idx in range(lback_idx, k + 2):
                                for p in self._orig_trans.get_atoms():
                                    timed_p = self.totime(p, idx)
                                    p_times = ExprAtTime.collect_times(self.i_mgr,
                                                                       timed_p)
                                    assert 1 <= len(p_times) <= 2, (p, p_times)
                                    if max(p_times) <= k + 1:
                                        if solver.get_value(timed_p).is_true():
                                            timed_p = self.i_mgr.Not(timed_p)
                                        else:
                                            assert solver.get_value(timed_p).is_false()
                                        ref.append(timed_p)
                        ref = self.i_mgr.Or(ref)
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
        try:
            for s in self.all_symbs:
                last_s = self.totime(s, last)
                lback_s = self.totime(s, lback)
                if s.symbol_type().is_bool_type():
                    solver.add_assertion(self.i_mgr.Iff(last_s, lback_s))
                else:
                    solver.add_assertion(self.i_mgr.Equals(last_s, lback_s))
            try:
                sat = solve_with_timeout(BMC._TIMEOUT, solver)
            except SolverReturnedUnknownResultError:
                sat = None
                log("\tBMC concretize timeout\n{}\n"
                    .format(to_smt2(solver.assertions)),
                    BMC._LOG_LVL)
            if sat is True:
                model = solver.get_model()
                return model
        finally:
            solver.pop()
        return None

    def _get_lback_index(self, model, last) -> int:
        # last state cannot be loop-back.
        for idx in range(last - 1, -1, -1):
            if model.get_value(self.totime(self.start_loop, idx)).is_true():
                return idx
        assert False

    def _get_lback_indexes(self, model, last) -> list:
        lback_idxs = []
        # last state cannot be loop-back
        for idx in range(last - 1, -1, -1):
            if model.get_value(self.totime(self.start_loop, idx)).is_true():
                lback_idxs.append(idx)
        return lback_idxs

    def _extend_loop_skeleton(self, last: int,
                              prev_model,
                              states: list,
                              trans: list,
                              bound: int) -> tuple:
        assert isinstance(last, int)
        assert last >= 0
        assert isinstance(states, list)
        assert isinstance(trans, list)
        assert isinstance(bound, int)
        assert bound > 0

        # max bound for BMC loop extension
        max_time = last + bound * (len(states) - 1)
        # monitor for trans entering in state.
        monitors = [self.i_mgr.Symbol("_m_trst{}".format(i), types.BOOL)
                    for i in range(1, len(states))]
        # monitors[i] -> seen all(trans[j-1] & states[j] for j <= i)
        c_trans = []
        prev_ms = []
        for idx, m in enumerate(monitors):
            # convert idx to state idx
            idx += 1
            x_m = symb_to_next(self.i_mgr, m)
            assert all(s.get_free_variables() <= self.all_symbs
                       for s in states[idx])

            trigger = self.i_mgr.And(*prev_ms,
                                     *(to_next(self.i_mgr, s, self.all_symbs)
                                       for s in states[idx]),
                                     *trans[idx - 1])
            c_trans.append(self.i_mgr.Implies(x_m, self.i_mgr.Or(m, trigger)))
            prev_ms.append(m)

        trans = self.i_mgr.And(self._orig_trans, *c_trans)
        del c_trans
        bad = monitors[-1]
        with Solver(env=self.i_env) as solver:
            # add init
            for m in monitors:
                solver.add_assertion(self.i_mgr.Not(self.totime(m, last)))
            for k in self.all_symbs:
                timed_k = self.totime(k, last)
                v = prev_model.get_value(timed_k)
                if v.is_true():
                    solver.add_assertion(timed_k)
                elif v.is_false():
                    solver.add_assertion(self.i_mgr.Not(timed_k))
                else:
                    solver.add_assertion(self.i_mgr.Equals(timed_k, v))

            start_assertion = len(solver.assertions)
            timed_symbs = [frozenset(self.totime(s, last)
                                     for s in self.all_symbs)]
            # add atoms of first state (useful for unsat cores)
            for p in states[0]:
                solver.add_assertion(self.totime(p, last))
            # we need to visit at least len(states) - 1 before reaching bad.
            for c_time in range(last, last + len(states) - 2):
                assert len(timed_symbs) == c_time - last + 1
                timed_symbs.append(frozenset(self.totime(s, c_time + 1)
                                             for s in self.all_symbs))
                # trans from c_time to c_time + 1
                solver.add_assertion(self.totime(trans, c_time))
                if __debug__:
                    solver.push()
                    solver.add_assertion(self.totime(bad, c_time + 1))
                    assert solver.solve() is False
                    solver.pop()

            for c_time in range(last + len(states) - 2, max_time):
                assert len(timed_symbs) == c_time - last + 1
                timed_symbs.append(frozenset(self.totime(s, c_time + 1)
                                             for s in self.all_symbs))
                solver.add_assertion(self.totime(trans, c_time))
                solver.push()
                solver.add_assertion(self.totime(bad, c_time + 1))
                try:
                    sat = solve_with_timeout(BMC._TIMEOUT, solver)
                except SolverReturnedUnknownResultError:
                    sat = None
                    log("\tBMC extension timeout\n{}\n"
                        .format(to_smt2(solver.assertions)),
                        BMC._LOG_LVL)
                    return None, None, None

                if sat is True:
                    loop_core = \
                        self.generalise(solver.assertions[start_assertion:],
                                        solver.get_model(), timed_symbs,
                                        last, c_time + 1)
                    if __debug__:
                        # loop_core -> original trans
                        _trans = [self.totime(self._orig_trans, _time)
                                  for _time in range(last, c_time + 1)]
                        _trans = self.i_mgr.And(_trans)
                        with Solver(env=self.i_env) as _solver:
                            _solver.add_assertion(self.i_mgr.Not(_trans))
                            for c in loop_core:
                                _solver.add_assertion(c)
                            sat = _solver.solve()
                            assert sat is False

                    return c_time + 1, loop_core, solver.get_model()
                solver.pop()
        return None, None, None

    def _model2trace(self, model, first: int, last: int,
                     to_out: bool = False) -> List[Dict[FNode, FNode]]:
        assert isinstance(first, int)
        assert isinstance(last, int)
        assert 0 <= first < last, (first, last)
        trace: List[Dict[FNode, FNode]] = [{} for _ in range(first, last + 1)]
        for c_time in range(first, last + 1):
            idx = c_time - first
            for s in self.all_symbs:
                timed_s = self.totime(s, c_time)
                v = model.get_value(timed_s)
                if to_out:
                    s = self.o_mgr.normalize(s)
                    v = self.o_mgr.normalize(v)
                assert s not in trace[idx], "{}".format(s)
                trace[idx][s] = v
        return trace
