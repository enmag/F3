from __future__ import annotations
from typing import Union, Optional, Tuple, List, Set, FrozenSet, Dict, \
    Iterator, Iterable
from itertools import chain
from io import StringIO

from pysmt.environment import Environment as PysmtEnv
from pysmt.fnode import FNode
import pysmt.typing as types
from pysmt.exceptions import SolverReturnedUnknownResultError

from expr_at_time import ExprAtTime
from rewritings import TimesDistributor
from canonize import Canonizer
from generalise import Generaliser
from multisolver import MultiSolver
from solver import get_solvers
from motzkin import motzkin_transpose
from efsolver import efsolve
from utils import log, symb_is_next, symb_to_next, to_next, \
    symb_to_curr, symb_is_curr, assign2fnodes, new_symb, linear_comb, \
    is_not_true, not_rel


class FunnelLoop:
    """Encapsulate a non-termination argument: list of connected funnels"""

    _PROPAGATE_MODE = 1
    _PROPAGATE_MAX_IT = 2
    _MIN_INEQS = 0
    _MAX_INEQS = 2
    _TIMEOUT = 25
    _FILTER_TIMEOUT = 5
    _LOG_LVL = 1

    @staticmethod
    def set_timeout(val: int) -> None:
        assert isinstance(val, int)
        FunnelLoop._TIMEOUT = val

    @staticmethod
    def get_timeout() -> int:
        return FunnelLoop._TIMEOUT

    @staticmethod
    def set_filter_timeout(val: int) -> None:
        assert isinstance(val, int)
        FunnelLoop._FILTER_TIMEOUT = val

    @staticmethod
    def get_filter_timeout() -> int:
        return FunnelLoop._FILTER_TIMEOUT

    @staticmethod
    def set_propagate_mode(val: int) -> None:
        assert isinstance(val, int), val
        FunnelLoop._PROPAGATE_MODE = val

    @staticmethod
    def get_propagate_mode() -> int:
        return FunnelLoop._PROPAGATE_MODE

    @staticmethod
    def set_propagate_max_it(val: int) -> None:
        assert isinstance(val, int), val
        assert val >= 1
        FunnelLoop._PROPAGATE_MAX_IT = val

    @staticmethod
    def get_propagate_max_it() -> int:
        return FunnelLoop._PROPAGATE_MAX_IT

    @staticmethod
    def set_min_ineqs(val: int) -> None:
        assert isinstance(val, int), val
        assert val >= 0
        FunnelLoop._MIN_INEQS = val

    @staticmethod
    def get_min_ineqs() -> int:
        return FunnelLoop._MIN_INEQS

    @staticmethod
    def set_max_ineqs(val: int) -> None:
        assert isinstance(val, int), val
        assert val >= 0
        FunnelLoop._MAX_INEQS = val

    @staticmethod
    def get_max_ineqs() -> int:
        return FunnelLoop._MAX_INEQS

    @staticmethod
    def factory(o_env: PysmtEnv, _symbs: FrozenSet[FNode],
                _trace: List[Dict[FNode, FNode]],
                _conc_assigns: List[Dict[FNode, FNode]],
                _abst_states: List[FrozenSet[FNode]],
                _abst_eqs: List[Dict[FNode, FNode]],
                _abst_trans: List[FrozenSet[FNode]],
                _hints_symbs: FrozenSet[FNode],
                _hints_states: List[FrozenSet[FNode]],
                _hints_eqs: List[Dict[FNode, FNode]],
                _hints_trans:  List[FrozenSet[FNode]],
                first: int,
                *args, **kwargs):
        """Generate different nontermination templates.

        Does not perform any heuristic reasoning,
        enumerates all templates compatible with the given trace:
        first try using only ConcFunnel,
        then a RFFunnel between every pair of candidate states.
        """
        assert isinstance(o_env, PysmtEnv)
        assert isinstance(_symbs, frozenset)
        assert all(isinstance(s, FNode) for s in _symbs)
        assert all(s in o_env.formula_manager.get_all_symbols() for s in _symbs)
        assert all(not ExprAtTime.is_timed_symb(o_env.formula_manager, s)
                   for s in _symbs)
        assert isinstance(_trace, List)
        assert all(isinstance(s, dict) for s in _trace)
        assert all(s in curr for curr in _trace for s in _symbs)
        assert all(not ExprAtTime.is_timed_symb(o_env.formula_manager, s)
                   for curr in _trace for s in curr)
        assert all(isinstance(v, FNode)
                   for curr in _trace for v in curr.values())
        assert all(v in o_env.formula_manager.formulae.values()
                   for curr in _trace for v in curr.values())
        assert all(v.is_constant() for curr in _trace for v in curr.values())
        assert isinstance(_conc_assigns, list)
        assert all(isinstance(assign, dict) for assign in _conc_assigns)
        assert all(isinstance(v, FNode)
                   for assign in _conc_assigns for v in assign.values())
        assert all(v.is_constant() for assign in _conc_assigns
                   for v in assign.values())
        assert isinstance(_abst_states, list)
        assert all(isinstance(state, (set, frozenset))
                   for state in _abst_states)
        assert all(isinstance(e, FNode)
                   for state in _abst_states for e in state)
        assert all(e in o_env.formula_manager.formulae.values()
                   for state in _abst_states for e in state)
        assert all(o_env.fvo.walk(e) <= _symbs
                   for state in _abst_states for e in state)
        assert isinstance(_abst_eqs, list)
        assert all(isinstance(eq, dict) for eq in _abst_eqs)
        assert all(k in frozenset(symb_to_next(o_env.formula_manager, s)
                                  for s in _symbs)
                   for eq in _abst_eqs for k in eq)
        assert all(isinstance(v, FNode)
                   for eq in _abst_eqs for v in eq.values())
        assert all(v in o_env.formula_manager.formulae.values()
                   for eq in _abst_eqs for v in eq.values())
        assert isinstance(_abst_trans, list)
        assert all(isinstance(t, (set, frozenset)) for t in _abst_trans)
        assert all(isinstance(t, FNode) for trans in _abst_trans for t in trans)
        assert all(o_env.fvo.walk(t) <=
                   _symbs | frozenset(symb_to_next(o_env.formula_manager, s)
                                      for s in _symbs)
                   for trans in _abst_trans for t in trans)
        assert isinstance(_hints_symbs, frozenset)
        assert all(isinstance(s, FNode) for s in _hints_symbs)
        assert all(s in o_env.formula_manager.get_all_symbols()
                   for s in _hints_symbs)
        assert all(symb_is_curr(s) for s in _hints_symbs)
        assert isinstance(_hints_states, list)
        assert all(isinstance(state, (set, frozenset))
                   for state in _hints_states)
        assert all(isinstance(e, FNode)
                   for state in _hints_states for e in state)
        assert all(e in o_env.formula_manager.formulae.values()
                   for state in _hints_states for e in state)
        assert all(o_env.fvo.walk(e) <= _symbs
                   for state in _hints_states for e in state)
        assert isinstance(_hints_eqs, list)
        assert all(isinstance(eq, dict) for eq in _hints_eqs)
        assert all(k in frozenset(symb_to_next(o_env.formula_manager, s)
                                  for s in _symbs)
                   for eq in _hints_eqs for k in eq)
        assert all(isinstance(v, FNode)
                   for eq in _hints_eqs for v in eq.values())
        assert all(v in o_env.formula_manager.formulae.values()
                   for eq in _hints_eqs for v in eq.values())
        assert isinstance(_hints_trans, list)
        assert all(isinstance(t, (set, frozenset)) for t in _hints_trans)
        assert all(isinstance(t, FNode)
                   for trans in _hints_trans for t in trans)
        assert all(o_env.fvo.walk(t) <=
                   _symbs | frozenset(symb_to_next(o_env.formula_manager, s)
                                      for s in _symbs)
                   for trans in _hints_trans for t in trans)
        assert isinstance(first, int)
        assert first >= 0
        assert len(_trace) == len(_abst_states)
        assert len(_conc_assigns) == len(_abst_states)
        assert len(_hints_states) == len(_abst_states)
        assert len(_abst_trans) == len(_abst_states) - 1
        assert len(_abst_eqs) == len(_abst_trans)
        assert len(_hints_trans) == len(_abst_trans)
        assert len(_hints_eqs) == len(_abst_trans)

        idx2concfunnel = [True] * (len(_abst_states) - 1)
        idx2key = [frozenset((_k, _v) for _k, _v in conc.items()
                             if not _k.symbol_name().startswith("_J"))
                   for conc in _conc_assigns]
        _idx2rffunnel = [[c - 1 for c in range(idx+1, len(_abst_states))
                          if idx2key[c] == idx2key[idx]]
                         for idx in range(len(_abst_states))]
        del idx2key
        for num_ineqs in range(FunnelLoop.get_min_ineqs(),
                               FunnelLoop.get_max_ineqs() + 1):
            env = PysmtEnv()
            norm = env.formula_manager.normalize
            totime = ExprAtTime(env=env, ignore_pref=Funnel.PREF)
            cn = Canonizer(env=env)
            td = TimesDistributor(env=env)
            # from o_env to env
            symbs = frozenset(norm(s) for s in _symbs)
            trace = [{norm(k): norm(v) for k, v in curr.items()}
                     for curr in _trace]
            # init = {norm(k): norm(v) for k, v in trace[0].items()}
            conc_assigns = [{norm(k): norm(v) for k, v in assign.items()}
                            for assign in _conc_assigns]
            abst_states = [frozenset(cn(norm(s)) for s in state)
                           for state in _abst_states]
            abst_eqs = [{cn(norm(k)): cn(norm(v)) for k, v in eq.items()}
                        for eq in _abst_eqs]
            abst_trans = [frozenset(cn(norm(t)) for t in abst_t)
                          for abst_t in _abst_trans]
            hints_symbs = frozenset(norm(s) for s in _hints_symbs)
            hints_states = [frozenset(cn(norm(s)) for s in state)
                            for state in _hints_states]
            hints_eqs = [{cn(norm(k)): cn(norm(v)) for k, v in eq.items()}
                         for eq in _hints_eqs]
            hints_trans = [frozenset(cn(norm(t)) for t in abst_t)
                           for abst_t in _hints_trans]

            idx2rffunnel = [[(i, abst_eqs[i], abst_trans[i],
                              hints_eqs[i], hints_trans[i])
                             for i in lst]
                            for lst in _idx2rffunnel]

            # single ConcFunnel
            nonterm_arg = FunnelLoop(env, td, cn, totime, init=trace[0])
            nonterm_arg.append(ConcFunnel(env, first,
                                          first + len(abst_states) - 1,
                                          symbs, conc_assigns,
                                          abst_states, abst_eqs, abst_trans,
                                          hints_symbs,
                                          hints_states, hints_eqs, hints_trans,
                                          num_ineqs, totime, cn))
            if nonterm_arg.set_loop() is True:
                yield nonterm_arg, num_ineqs

            yield from \
                FunnelLoop._generate_nonterm_args(
                    env, first, symbs, trace, conc_assigns,
                    abst_states, abst_eqs, abst_trans,
                    hints_symbs,
                    hints_states, hints_eqs, hints_trans,
                    num_ineqs, idx2concfunnel, idx2rffunnel,
                    totime, td, cn)

    @staticmethod
    def _generate_nonterm_args(
            env: PysmtEnv, first: int, symbs: FrozenSet[FNode],
            trace: List[Dict[FNode, FNode]],
            _conc_assigns: List[Dict[FNode, FNode]],
            _abst_states: List[FrozenSet[FNode]],
            _abst_eqs: List[Dict[FNode, FNode]],
            _abst_trans: List[FrozenSet[FNode]],
            hints_symbs: FrozenSet[FNode],
            _hints_states: List[FrozenSet[FNode]],
            _hints_eqs: List[Dict[FNode, FNode]],
            _hints_trans: List[FrozenSet[FNode]],
            num_ineqs: int,
            idx2concfunnel: List[bool],
            idx2rffunnel: List[List[Tuple[int,
                                          Dict[FNode, FNode], FrozenSet[FNode],
                                          Dict[FNode, FNode], FrozenSet[FNode]]]],
            totime: ExprAtTime, td: TimesDistributor, cn: Canonizer):
        assert len(trace) == len(_abst_states)
        assert _conc_assigns[0] == _conc_assigns[-1]

        for n_rffunnels in range(1, len(_abst_states)):
            for lst in \
                FunnelLoop._generate_start_end_idx(0, n_rffunnels,
                                                   len(_abst_states),
                                                   idx2concfunnel,
                                                   idx2rffunnel):
                assert isinstance(lst, list)
                assert all(isinstance(el, tuple) for el in lst)
                assert all(len(el) == 6 for el in lst)
                assert all(isinstance(el[0], int) for el in lst)
                assert all(0 <= el[0] < len(trace) for el in lst)
                assert all(isinstance(el[1], int) for el in lst)
                assert all(0 <= el[1] < len(trace) for el in lst)
                assert all(isinstance(el[2], dict) for el in lst)
                assert all(isinstance(k, FNode) for el in lst for k in el[2])
                assert all(isinstance(v, FNode)
                           for el in lst for v in el[2].values())
                assert all(isinstance(el[3], frozenset) for el in lst)
                assert all(isinstance(pred, FNode)
                           for el in lst for pred in el[3])
                assert all(isinstance(el[4], dict) for el in lst)
                assert all(isinstance(k, FNode) for el in lst for k in el[4])
                assert all(isinstance(v, FNode)
                           for el in lst for v in el[4].values())
                assert all(isinstance(el[5], frozenset) for el in lst)
                assert all(isinstance(pred, FNode)
                           for el in lst for pred in el[5])

                last_end = 0
                # bring first RFFunnel at the beginning.
                offset = lst[0][0] if lst else 0
                conc_assigns = _conc_assigns[offset: -1] + \
                    _conc_assigns[: offset + 1]
                abst_states = _abst_states[offset:]
                abst_states[-1] = abst_states[-1] | _abst_states[0]
                abst_states += _abst_states[1: offset + 1]
                hints_states = _hints_states[offset:]
                hints_states[-1] = hints_states[-1] | _hints_states[0]
                hints_states += _hints_states[1: offset + 1]
                assert offset == 0 or abst_states[0] == abst_states[-1]
                assert offset == 0 or hints_states[0] == hints_states[-1]
                assert len(abst_states) == len(conc_assigns)
                assert len(abst_states) == len(_abst_states)
                assert len(hints_states) == len(abst_states)
                abst_eqs = _abst_eqs[offset:] + _abst_eqs[: offset]
                hints_eqs = _hints_eqs[offset:] + _hints_eqs[: offset]
                abst_trans = _abst_trans[offset:] + _abst_trans[: offset]
                hints_trans = _hints_trans[offset:] + _hints_trans[: offset]

                nonterm_arg = FunnelLoop(env, td, cn, totime, offset=offset)
                nonterm_arg.set_init(trace[offset])
                for start, end, a_eqs, a_ineqs, h_eqs, h_ineqs in lst:
                    start -= offset
                    end -= offset
                    assert start >= 0
                    assert end >= 0
                    assert end < len(abst_states)
                    assert end >= start

                    if start > last_end:
                        assert all(idx2concfunnel[last_end + offset:
                                                  start + offset])
                        nonterm_arg.append(
                            ConcFunnel(env, first + last_end, first + start,
                                       symbs, conc_assigns[last_end: start + 1],
                                       abst_states[last_end: start + 1],
                                       abst_eqs[last_end: start],
                                       abst_trans[last_end: start],
                                       hints_symbs,
                                       hints_states[last_end: start + 1],
                                       hints_eqs[last_end: start],
                                       hints_trans[last_end: start],
                                       num_ineqs, totime, cn))
                    rf_t_abst_eqs = abst_eqs[start: end] + [a_eqs]
                    rf_t_abst_ineqs = abst_trans[start: end] + [a_ineqs]
                    rf_t_hints_eqs = hints_eqs[start: end] + [h_eqs]
                    rf_t_hints_ineqs = hints_trans[start: end] + [h_ineqs]
                    nonterm_arg.append(
                        RFFunnel(env, first + start, first + end,
                                 symbs,
                                 conc_assigns[start: end + 1],
                                 abst_states[start: end + 1],
                                 rf_t_abst_eqs,
                                 rf_t_abst_ineqs,
                                 hints_symbs,
                                 hints_states[start: end + 1],
                                 rf_t_hints_eqs,
                                 rf_t_hints_ineqs,
                                 num_ineqs, totime, cn))
                    last_end = end

                if last_end < len(abst_states) - 1:
                    nonterm_arg.append(ConcFunnel(
                        env, first + last_end, first + len(abst_states) - 1,
                        symbs,
                        conc_assigns[last_end:],
                        abst_states[last_end:],
                        abst_eqs[last_end:],
                        abst_trans[last_end:],
                        hints_symbs,
                        hints_states[last_end:],
                        hints_eqs[last_end:],
                        hints_trans[last_end:],
                        num_ineqs, totime, cn))

                if nonterm_arg.set_loop() is True:
                    yield nonterm_arg, num_ineqs

    @staticmethod
    def _generate_start_end_idx(
            start: int, n_rf_funnels: int, num_states: int,
            idx2concf: List[bool],
            idx2rff: List[List[Tuple[int,
                                     Dict[FNode, FNode], FrozenSet[FNode],
                                     Dict[FNode, FNode], FrozenSet[FNode]]]]):
        assert isinstance(start, int)
        assert isinstance(n_rf_funnels, int)
        assert isinstance(num_states, int)
        assert start >= 0
        assert n_rf_funnels >= 0
        assert num_states > 1
        assert isinstance(idx2concf, list)
        assert len(idx2concf) == num_states - 1
        assert all(isinstance(el, bool) for el in idx2concf)
        assert isinstance(idx2rff, list)
        assert len(idx2rff) == num_states
        assert all(isinstance(it, list) for it in idx2rff)
        assert all(isinstance(el, tuple) for it in idx2rff
                   for el in it)
        assert all(len(el) == 5 for it in idx2rff for el in it)
        assert all(isinstance(el[0], int) for it in idx2rff
                   for el in it)
        assert all(isinstance(el[1], dict) for it in idx2rff
                   for el in it)
        assert all(isinstance(el[2], frozenset) for it in idx2rff
                   for el in it)
        assert all(isinstance(el[3], dict) for it in idx2rff
                   for el in it)
        assert all(isinstance(el[4], frozenset) for it in idx2rff
                   for el in it)
        assert all(isinstance(el, FNode)
                   for lst in idx2rff for it in lst
                   for el in it[1])
        assert all(isinstance(el, FNode)
                   for lst in idx2rff for it in lst
                   for el in it[1].values())
        assert all(isinstance(el, FNode)
                   for lst in idx2rff for it in lst
                   for el in it[2])
        assert all(isinstance(el, FNode)
                   for lst in idx2rff for it in lst
                   for el in it[3])
        assert all(isinstance(el, FNode)
                   for lst in idx2rff for it in lst
                   for el in it[3].values())
        assert all(isinstance(el, FNode)
                   for lst in idx2rff for it in lst
                   for el in it[4])

        def _gen_start_end_idx(start: int, n_rf_funnels: int,
                               num_states, idx2concf: list, idx2rff: list,
                               start_end_idx: list) \
                        -> Iterator[List[Tuple[int, int,
                                               Dict[FNode, FNode],
                                               FrozenSet[FNode],
                                               Dict[FNode, FNode],
                                               FrozenSet[FNode]]]]:
            last_end = start_end_idx[-1][1] if start_end_idx else 0
            for c_start in range(start, num_states):
                if not all(idx2concf[last_end: c_start]):
                    continue
                for c_end, eqs, neqs, h_eqs, h_neqs in idx2rff[c_start]:
                    assert isinstance(c_end, int)
                    assert isinstance(eqs, dict)
                    assert isinstance(neqs, frozenset)
                    assert isinstance(h_eqs, dict)
                    assert isinstance(h_neqs, frozenset)
                    start_end_idx.append((c_start, c_end, eqs, neqs,
                                          h_eqs, h_neqs))
                    if n_rf_funnels == 1:
                        if all(idx2concf[c_end+1:]):
                            yield start_end_idx
                    else:
                        yield from _gen_start_end_idx(c_end + 1,
                                                      n_rf_funnels - 1,
                                                      num_states,
                                                      idx2concf, idx2rff,
                                                      start_end_idx)
                    start_end_idx.pop()

        yield from _gen_start_end_idx(start, n_rf_funnels, num_states,
                                      idx2concf, idx2rff, [])

    def __init__(self, env: PysmtEnv, td: TimesDistributor,
                 cn: Canonizer, totime: ExprAtTime,
                 init: Optional[Dict[FNode, FNode]] = None, offset: int = 0):
        assert isinstance(env, PysmtEnv)
        assert isinstance(td, TimesDistributor)
        assert isinstance(cn, Canonizer)
        assert isinstance(totime, ExprAtTime)
        assert td.env == env
        assert cn.env == env
        assert totime.env == env

        self.env = env
        self.td = td
        self.cn = cn
        self.totime = totime
        self.offset = offset
        self.parameters: Union[Set[FNode], FrozenSet[FNode]] = set()
        self._funnels: List[Funnel] = []
        self._init = init if init else {}

    def set_init(self, init: Dict[FNode, FNode]) -> None:
        assert isinstance(init, dict)
        assert all(k in self.env.formula_manager.get_all_symbols()
                   for k in init)
        assert all(v in self.env.formula_manager.formulae.values()
                   for v in init.values())
        assert all(v.is_constant() for v in init.values())
        self._init = init

    def append(self, funnel: Funnel) -> None:
        """Ensure prev_f.last -> curr_f.first"""
        assert isinstance(funnel, Funnel)
        assert funnel.env == self.env
        assert isinstance(self.parameters, set)

        self.parameters.update(funnel.parameters)
        if self._funnels:
            # link funnels together.
            last = self._funnels[-1]
            assert last.last == funnel.first
            assert last.states[-1] == funnel.states[0]
            assert last.assigns[-1] == funnel.assigns[0]
            assert funnel.hint_states[-1] == last.hint_states[0]
            funnel.strengthen_state(0, *last.last_ineqs)
            last.last_ineqs.extend(funnel.first_ineqs)
        self._funnels.append(funnel)
        assert len(self._funnels) < 2 or \
            self._funnels[-1].first == self._funnels[-2].last

    def set_loop(self) -> bool:
        """Ensure last_f.last -> first_f.first.
        Returns false if loop unrealizable, True otherwise"""
        assert len(self._funnels) >= 1
        self.parameters = frozenset(self.parameters)
        first_f = self._funnels[0]
        last_f = self._funnels[-1]
        assert last_f.last - first_f.first >= 1
        assert last_f.assigns[-1] == first_f.assigns[0]

        # strengthen first state with last state
        first_f.strengthen_state(0, *last_f.states[-1])
        first_f.strengthen_hint_state(0, *last_f.hint_states[-1])

        propagate_mode = FunnelLoop.get_propagate_mode()
        bound = FunnelLoop.get_propagate_max_it()
        assert propagate_mode in {0, 1, 2}
        if propagate_mode > 0 and bound > 0:
            false = self.env.formula_manager.FALSE()
            preds = frozenset(chain(first_f.first_ineqs,
                                    first_f.states[0]))
            h_preds = frozenset(first_f.hint_states[0])
            propagate_fs = [f.backward_propagate_partial
                            if propagate_mode == 1 else f.backward_propagate
                            for f in self._funnels]
            assert all(self.cn(p) == p for p in preds)
            assert all(self.cn(p) == p for p in h_preds)
            prev_f = first_f
            pair_list = list(reversed(list(zip(self._funnels, propagate_fs))))
            it = 0
            while it < bound:
                it += 1
                for f, propagate in pair_list:
                    (preds, h_preds), (keep, h_keep) = propagate(preds, h_preds)
                    assert all(self.cn(p) == p for p in preds)
                    assert all(self.cn(p) == p for p in keep)
                    assert all(self.cn(p) == p for p in h_preds)
                    assert all(self.cn(p) == p for p in h_keep)

                    f.strengthen_state(0, *preds)
                    f.strengthen_hint_state(0, *h_preds)
                    prev_f.strengthen_state(0, *keep)
                    f.last_ineqs.extend(keep)
                    prev_f.strengthen_hint_state(0, *h_keep)
                    prev_f = f
                    if false in preds or false in h_preds:
                        return False

            assert all(p in frozenset(chain(first_f.states[0],
                                            first_f.first_ineqs))
                       for p in preds)
            assert all(p in first_f.hint_states[0] for p in h_preds)
        last_f.last_ineqs.extend(first_f.first_ineqs)
        # last_f must imply first state.
        last_f.strengthen_state(-1, *first_f.states[0])
        last_f.strengthen_hint_state(-1, *first_f.hint_states[0])
        return True

    def ef_instantiate(self, extra: Optional[Iterable[FNode]] = None):
        res = None
        mgr = self.env.formula_manager
        simpl = self.env.simplifier.simplify
        subst = self.env.substituter.substitute
        generalise = Generaliser(self.env, self.cn, self.totime)
        get_free_vars = self.env.fvo.walk
        log("\tTry solve EF-constraints", FunnelLoop._LOG_LVL)
        try:
            solver_it = iter(get_solvers())
            solver = next(solver_it)
            log(f"\tUsing solver {solver} for EF-constraints",
                FunnelLoop._LOG_LVL)
            first_f = self._funnels[0]
            constrs = list(filter(is_not_true,
                                  (simpl(subst(ineq, self._init))
                                   for ineq in first_f.first_ineqs)))
            constrs.extend(filter(is_not_true,
                                  (simpl(subst(abst_s, self._init))
                                   for abst_s in first_f.states[0])))
            constrs.extend(chain.from_iterable(f.constraints
                                               for f in self._funnels))
            if extra:
                constrs.extend(extra)

            constrs = mgr.And(constrs)
            symbs = get_free_vars(constrs) - self.parameters
            res, learn = efsolve(self.env, self.parameters, symbs,
                                 constrs, esolver_name=solver,
                                 fsolver_name=solver,
                                 generalise=generalise)
            constrs = mgr.And(constrs, mgr.And(learn))
            while res is None:
                solver = next(solver_it)
                log(f"\tUsing solver {solver} for EF-constraints",
                    FunnelLoop._LOG_LVL)
                res, c_learn = efsolve(self.env, self.parameters, symbs,
                                       constrs,
                                       esolver_name=solver,
                                       fsolver_name=solver)
                constrs = mgr.And(constrs, mgr.And(c_learn))
                learn.extend(c_learn)
        except StopIteration:
            return None, learn
        return res, learn

    def motzkin_instantiate(self, extra: Optional[Iterable[FNode]] = None):
        res = None
        log("\tUsing motzkin-constraints", FunnelLoop._LOG_LVL)
        with MultiSolver(self.env, FunnelLoop.get_timeout(),
                         log_lvl=FunnelLoop._LOG_LVL) as solver:
            if extra:
                for c in extra:
                    assert c in self.env.formula_manager.formulae.values()
                    solver.add_assertion(c)
            for c in self.generate_motzkin_constr():
                assert c in self.env.formula_manager.formulae.values()
                solver.add_assertion(c)

            # DEBUG
            # mgr = self.env.formula_manager
            # from fractions import Fraction
            # r_m1 = mgr.Real(-1)
            # r_0 = mgr.Real(0)
            # r_9_d_10 = mgr.Real(Fraction(9, 10))
            # r_1 = mgr.Real(1)

            # i_m1 = mgr.Int(-1)
            # i_0 = mgr.Int(0)
            # i_1 = mgr.Int(1)
            # i_2 = mgr.Int(2)

            # debug_substs = {
            #     # RFFun0 rank fun
            #     mgr.Symbol("_fun_d8", types.REAL): r_9_d_10,
            #     mgr.Symbol("_fun_k4", types.REAL): r_m1,
            #     mgr.Symbol("_fun_c5", types.REAL): r_m1,
            #     mgr.Symbol("_fun_c6", types.REAL): r_1,
            #     mgr.Symbol("_fun_c7", types.REAL): r_0,
            #     # RFFun0 invar
            #     mgr.Symbol("_fun_k0", types.INT): i_1,
            #     mgr.Symbol("_fun_c2", types.INT): i_1,
            #     mgr.Symbol("_fun_c1", types.INT): i_m1,
            #     mgr.Symbol("_fun_c3", types.INT): i_0,
            #     # ConcFun 1 invar
            #     mgr.Symbol("_fun_c10", types.INT): i_0,
            #     mgr.Symbol("_fun_c11", types.INT): i_0,
            #     mgr.Symbol("_fun_c12", types.INT): i_0,
            #     mgr.Symbol("_fun_k9", types.INT): i_0,
            #     # RFFun 2 rank fun
            #     mgr.Symbol("_fun_d21", types.REAL): r_9_d_10,
            #     mgr.Symbol("_fun_k17", types.REAL): r_m1,
            #     mgr.Symbol("_fun_c18", types.REAL): r_1,
            #     mgr.Symbol("_fun_c19", types.REAL): r_0,
            #     mgr.Symbol("_fun_c20", types.REAL): r_m1,
            #     # RFFun 2 invar
            #     mgr.Symbol("_fun_k13", types.INT): i_0,
            #     mgr.Symbol("_fun_c14", types.INT): i_0,
            #     mgr.Symbol("_fun_c15", types.INT): i_0,
            #     mgr.Symbol("_fun_c16", types.INT): i_0,
            #     # ConcFun3 invar
            #     mgr.Symbol("_fun_k22", types.INT): i_0,
            #     mgr.Symbol("_fun_c23", types.INT): i_0,
            #     mgr.Symbol("_fun_c24", types.INT): i_0,
            #     mgr.Symbol("_fun_c25", types.INT): i_0,
            #     # assign b0[7]
            #     mgr.Symbol("_fun_k26", types.INT): i_2,
            #     mgr.Symbol("_fun_c27", types.INT): i_1,
            #     mgr.Symbol("_fun_c28", types.INT): i_0,
            #     mgr.Symbol("_fun_c29", types.INT): i_0,
            # }
            # for k, v in debug_substs.items():
            #     solver.add_assertion(mgr.Equals(k, v))
            # END DEBUG
            try:
                res = solver.solve()
            except SolverReturnedUnknownResultError:
                log("\t\tMotzkinUnranker timeout", FunnelLoop._LOG_LVL)
                res = None
            if res is True:
                return solver.get_values(self.parameters)
        assert res is None or res is False
        return res

    def generate_motzkin_constr(self) -> Iterator[FNode]:
        """Sequence of constraints generated via Motzkin transposition"""
        td = self.td
        simpl = self.env.simplifier.simplify
        subst = self.env.substituter.substitute
        mgr = self.env.formula_manager
        get_free_vars = self.env.fvo.walk

        # # DEBUG parameter assignments for 2_loops2a 1 ineq
        # from fractions import Fraction
        # r_m1 = mgr.Real(-1)
        # r_0 = mgr.Real(0)
        # r_9_d_10 = mgr.Real(Fraction(9, 10))
        # r_1 = mgr.Real(1)

        # i_m1 = mgr.Int(-1)
        # i_0 = mgr.Int(0)
        # i_1 = mgr.Int(1)
        # i_2 = mgr.Int(2)
        # debug_substs = {
        #     # RFFun0 rank fun
        #     mgr.Symbol("_fun_d8", types.REAL): r_9_d_10,
        #     mgr.Symbol("_fun_k4", types.REAL): r_m1,
        #     mgr.Symbol("_fun_c5", types.REAL): r_m1,
        #     mgr.Symbol("_fun_c6", types.REAL): r_1,
        #     mgr.Symbol("_fun_c7", types.REAL): r_0,
        #     # RFFun0 invar
        #     mgr.Symbol("_fun_k0", types.INT): i_1,
        #     mgr.Symbol("_fun_c2", types.INT): i_1,
        #     mgr.Symbol("_fun_c1", types.INT): i_m1,
        #     mgr.Symbol("_fun_c3", types.INT): i_0,
        #     # ConcFun 1 invar
        #     mgr.Symbol("_fun_c10", types.INT): i_0,
        #     mgr.Symbol("_fun_c11", types.INT): i_0,
        #     mgr.Symbol("_fun_c12", types.INT): i_0,
        #     mgr.Symbol("_fun_k9", types.INT): i_0,
        #     # RFFun 2 rank fun
        #     mgr.Symbol("_fun_d21", types.REAL): r_9_d_10,
        #     mgr.Symbol("_fun_k17", types.REAL): r_m1,
        #     mgr.Symbol("_fun_c18", types.REAL): r_1,
        #     mgr.Symbol("_fun_c19", types.REAL): r_0,
        #     mgr.Symbol("_fun_c20", types.REAL): r_m1,
        #     # RFFun 2 invar
        #     mgr.Symbol("_fun_k13", types.INT): i_0,
        #     mgr.Symbol("_fun_c14", types.INT): i_0,
        #     mgr.Symbol("_fun_c15", types.INT): i_0,
        #     mgr.Symbol("_fun_c16", types.INT): i_0,
        #     # ConcFun3 invar
        #     mgr.Symbol("_fun_k22", types.INT): i_0,
        #     mgr.Symbol("_fun_c23", types.INT): i_0,
        #     mgr.Symbol("_fun_c24", types.INT): i_0,
        #     mgr.Symbol("_fun_c25", types.INT): i_0,
        #     # assign b0[7]
        #     mgr.Symbol("_fun_k26", types.INT): i_2,
        #     mgr.Symbol("_fun_c27", types.INT): i_1,
        #     mgr.Symbol("_fun_c28", types.INT): i_0,
        #     mgr.Symbol("_fun_c29", types.INT): i_0,
        # }
        # # END DEBUG

        first_f = self._funnels[0]
        # init -> first_f.first
        first = [simpl(subst(ineq, self._init))
                 for ineq in first_f.first_ineqs]

        first.extend(simpl(subst(abst_s, self._init))
                     for abst_s in first_f.states[0])
        assert all(get_free_vars(constr) <= self.parameters
                   for constr in first)

        # # DEBUG
        # for f in first:
        #     assert simpl(subst(f, debug_substs)).is_true(), f.serialize()
        # dbg_constrs = []
        # # END DEBUG

        yield from filter(lambda x: not x.is_true(), first)

        for f in self._funnels:
            for lhs, rhs in f.implications:
                assert isinstance(lhs, frozenset), lhs
                assert isinstance(rhs, frozenset), rhs
                assert len(lhs) + len(rhs) > 0
                assert all(isinstance(l, FNode) for l in lhs)
                assert all(not l.is_false() for l in lhs)
                assert all(isinstance(r, FNode) for r in rhs)
                # # DEBUG
                # # print("\nImplication:")
                # # print("{} ->\n  {}\n".format([l.serialize() for l in lhs],
                # #                              [r.serialize() for r in rhs]))

                # dbg_c = mgr.Implies(mgr.And(lhs),
                #                     mgr.And(rhs))
                # # print("{}\n".format(dbg_c.serialize()))
                # dbg_c = simpl(subst(dbg_c, debug_substs))
                # # print("{}\n".format(dbg_c.serialize()))
                # dbg_constrs.append(dbg_c)
                # with Solver(env=self.env) as solver:
                #     # valid dbg_c
                #     solver.add_assertion(mgr.Not(dbg_c))
                #     sat = solver.solve()
                #     if sat is True:
                #         import pdb
                #         pdb.set_trace()
                #     assert sat is False, dbg_c.serialize()
                # # END DEBUG

                if all(get_free_vars(s) <= self.parameters
                       for s in chain(lhs, rhs)):
                    constr = simpl(mgr.Implies(mgr.And(lhs),
                                               mgr.And(rhs)))
                    yield constr
                else:
                    if all(not r.is_true() for r in rhs):
                        constrs = frozenset(filter(lambda x: not x.is_true(),
                                                   chain(lhs,
                                                         (f.not_rel(r)
                                                          for r in rhs))))
                        yield from motzkin_transpose(self.env, constrs,
                                                     td, self.parameters)
        # # DEBUG
        # with Solver(env=self.env) as solver:
        #     mgr = self.env.formula_manager
        #     _dbg_constrs = mgr.Not(mgr.And(dbg_constrs))
        #     solver.add_assertion(_dbg_constrs)
        #     sat = solver.solve()
        #     if sat is True:
        #         model = solver.get_model()
        #         for impl in dbg_constrs:
        #             print("{} : {}".format(model[impl], impl.serialize()))
        #             if model[impl].is_false():
        #                 for c_time in range(4, 9):
        #                     for s in self._funnels[0].all_symbs:
        #                         s = self.totime.walk(s, c_time)
        #                         print("{} : {}".format(s, model[s]))
        #                         import pdb
        #                         pdb.set_trace()
        #                         print(to_smt2(env, mgr.Not(impl)))
        #     else:
        #         print("UNSAT")
        # # END DEBUG

    def describe(self, model: Optional[dict] = None,
                 indent: Optional[str] = None) -> str:
        """Return string describing current non-termination argument"""
        if not model:
            model = {p: p for p in self.parameters}
        assert isinstance(model, dict)
        indent = indent if indent else ""
        assert isinstance(indent, str)
        serialize = self.env.serializer.serialize
        with StringIO() as buf:
            for f in self._funnels:
                f.describe(model, indent, buf)
            buf.write(f"\tstarting from: {', '.join(f'{serialize(k)} : {serialize(v)}' for k, v in self._init.items())}\n")
            return buf.getvalue()

    def desc_template(self) -> str:
        """Return string description of current template"""
        res = "; ".join(f"{type(f).__name__}(first: {f.first}, last: {f.last})"
                        for f in self._funnels)
        res += f", offset: {self.offset}"
        return res

    def to_smv(self, trans: FNode, fair: FNode, model: dict, buf,
               orig_ltl: Optional[str] = None) -> None:
        from smv_printer import SMVPrinter
        assert len(self._funnels) > 0
        assert orig_ltl is None or isinstance(orig_ltl, str)

        symbs = self._funnels[0].all_symbs
        expr_print = SMVPrinter(buf, env=self.env)
        mgr = self.env.formula_manager
        serialize = self.env.serializer.serialize
        state_var = "_f_state_"
        orig_trans_symb = "_orig_trans_"
        first = self._funnels[0].first
        last = self._funnels[-1].last
        buf.write("MODULE main\n")
        buf.write("  INVARSPEC NAME NOT_EMPTY := "
                  f"!({state_var} = {last} & next({state_var}) = {first});\n")
        buf.write("  INVARSPEC NAME UNDERAPPROX := "
                  f"({first} <= {state_var} & {state_var} < {last}) -> {orig_trans_symb}")
        buf.write(";\n")
        buf.write("  LTLSPEC NAME GF_FAIR := ")
        if orig_ltl is None:
            buf.write("G F ")
            expr_print.printer(fair)
        else:
            buf.write("! ")
            buf.write(orig_ltl)

        buf.write(f";\n\n  DEFINE\n    {orig_trans_symb} := ")
        expr_print.printer(trans)
        buf.write(";\n  VAR\n")
        buf.write(f"    {state_var} : {first}..{last};\n")
        for s in symbs:
            buf.write("    ")
            expr_print.printer(s)
            buf.write(" : ")
            expr_print.smvtype(s.symbol_type())
            buf.write(";\n")
        buf.write("\n  -- initial state\n  INIT ")
        expr_print.printer(mgr.And(assign2fnodes(self.env, self._init)))

        buf.write(";\n\n  -- constant assignments\n")
        for f in self._funnels:
            for idx, assign in enumerate(f.assigns[:-1]):
                c_time = f.first + idx
                buf.write(f"  INVAR {state_var} = {c_time} -> (")
                expr_print.printer(mgr.And(assign2fnodes(self.env, assign)))
                buf.write(");\n")
        buf.write(f"  INVAR {state_var} = {self._funnels[-1].last} -> (")
        assign = self._funnels[-1].assigns[-1]
        expr_print.printer(mgr.And(assign2fnodes(self.env, assign)))
        buf.write(f");\n\n  -- control flow graph for `{state_var}`\n")

        buf.write(f"  ASSIGN\n    init({state_var}) := {first};\n")
        cfgs = [[] for _ in range(last - first)]
        for f in self._funnels:
            c_first = f.first - first
            for idx, c_cfg in enumerate(f.cfg(model)):
                cfgs[idx + c_first].append(c_cfg)
        buf.write(f"    next({state_var}) :=\n      case\n")
        for idx, cfg in enumerate(cfgs):
            c_time = idx + first
            for x_time, cond in cfg:
                buf.write(f"        {state_var} = {c_time}")
                if cond:
                    buf.write(" & ")
                    expr_print.printer(cond)
                buf.write(f" : {x_time};\n")
        buf.write(f"        {state_var} = {last} : {first};\n")
        buf.write(f"        TRUE : {state_var};\n")
        buf.write("      esac;\n\n  -- link last with first state\n")

        buf.write(f"  TRANS ({state_var} = {last} & "
                  f"next({state_var}) = {first}) -> "
                  "{};\n".format(" & ".join(f"next({serialize(s)}) = {serialize(s)}"
                                            for s in symbs
                                            if not s.symbol_name()
                                            .startswith("_J"))))
        for f in self._funnels:
            f.to_smv(model, state_var, buf, expr_print)

    def _debug_check(self, model) -> Tuple[bool, Optional[str]]:
        from solver import Solver
        subst = self.env.substituter.substitute
        simpl = self.env.simplifier.simplify
        serialize = self.env.serializer.serialize
        mgr = self.env.formula_manager
        first_f = self._funnels[0]
        with Solver(env=self.env) as solver:
            first_c = [simpl(subst(s, model)) for s in first_f.states[0]]
            first_c.extend([simpl(subst(s, model))
                            for s in first_f.first_ineqs])
            first_c = mgr.And(first_c)
            solver.add_assertion(first_c)
            if solver.solve() is not True:
                return False, f"First UNSAT: {serialize(first_c)}"
            for init_assign in assign2fnodes(self.env, self._init):
                solver.add_assertion(init_assign)
            if solver.solve() is not True:
                return False, f"Init not in first: {self._init}"

        for f_num, f in enumerate(self._funnels):
            for c in f.constraints:
                curr = simpl(subst(c, model))
                with Solver(env=self.env) as solver:
                    # each constraint must be valid.
                    solver.add_assertion(mgr.Not(curr))
                    if solver.solve() is not False:
                        return False, f"Funnel number {f_num}, sat: {serialize(c)}"
        return True, None


class Funnel:
    """Underapproximation leading from src to dst"""

    PREF = "_fun"

    def __init__(self, env: PysmtEnv, src_idx: int, dst_idx: int,
                 symbols: FrozenSet[FNode],
                 conc_assigns: List[Dict[FNode, FNode]],
                 states: List[FrozenSet[FNode]],
                 trans_eqs: List[Dict[FNode, FNode]],
                 trans: List[FrozenSet[FNode]],
                 hint_symbs: FrozenSet[FNode],
                 hint_states: List[FrozenSet[FNode]],
                 hint_eqs: List[Dict[FNode, FNode]],
                 hint_trans: List[FrozenSet[FNode]],
                 num_ineqs: int, totime: ExprAtTime, cn: Canonizer):
        assert isinstance(env, PysmtEnv)
        assert isinstance(src_idx, int)
        assert isinstance(dst_idx, int)
        assert isinstance(symbols, frozenset)
        assert isinstance(conc_assigns, list)
        assert isinstance(states, list)
        assert isinstance(trans_eqs, list)
        assert isinstance(trans, list)
        assert isinstance(hint_symbs, frozenset)
        assert isinstance(hint_states, list)
        assert isinstance(hint_eqs, list)
        assert isinstance(hint_trans, list)
        assert isinstance(num_ineqs, int)
        assert isinstance(totime, ExprAtTime)
        assert isinstance(cn, Canonizer)
        assert cn.env == env
        assert totime.env == env

        assert num_ineqs >= 0
        assert src_idx >= 0
        assert dst_idx >= src_idx
        assert all(isinstance(s, FNode) for s in symbols)
        assert all(s.is_symbol() for s in symbols)
        assert all(s in env.formula_manager.get_all_symbols() for s in symbols)
        assert all(s in env.formula_manager.formulae.values() for s in symbols)
        assert all(isinstance(eqs, dict) for eqs in conc_assigns)
        assert all(isinstance(s, FNode) for eqs in conc_assigns
                   for s in eqs.keys())
        assert all(s in env.formula_manager.formulae.values()
                   for eqs in conc_assigns for s in eqs.keys())
        assert all(v in env.formula_manager.formulae.values()
                   for eqs in conc_assigns for v in eqs.values())
        assert all(isinstance(state, (list, set, frozenset))
                   for state in states)
        assert all(isinstance(s, FNode) for state in states for s in state)
        assert all(len(env.ao.get_atoms(s)) == 1 for state in states for s in state)
        assert all(s in env.formula_manager.formulae.values()
                   for state in states for s in state)
        assert all(cn(s) == s for state in states for s in state)
        assert all(isinstance(eqs, dict) for eqs in trans_eqs)
        assert all(isinstance(s, FNode) for eqs in trans_eqs
                   for s in eqs.keys())
        assert all(s.is_symbol() for eqs in trans_eqs
                   for s in eqs.keys())
        assert all(s in env.formula_manager.formulae.values()
                   for eqs in trans_eqs for s in eqs.keys())
        assert all(isinstance(s, FNode) for eqs in trans_eqs
                   for s in eqs.values())
        assert all(s in env.formula_manager.formulae.values()
                   for eqs in trans_eqs for s in eqs.values())
        assert all(cn(s) == s for eqs in trans_eqs for s in eqs.values())
        assert all(isinstance(s_trans, (list, set, frozenset))
                   for s_trans in trans)
        assert all(isinstance(t, FNode)
                   for s_trans in trans for t in s_trans)
        assert all(len(env.ao.get_atoms(t)) == 1
                   for s_trans in trans for t in s_trans)
        assert all(t in env.formula_manager.formulae.values()
                   for s_trans in trans for t in s_trans)
        assert all(cn(t) == t for s_trans in trans for t in s_trans)
        assert len(states) == dst_idx - src_idx + 1, (len(states), src_idx,
                                                      dst_idx)
        assert len(conc_assigns) == len(states)
        assert len(trans) == len(states) - 1 or len(trans) == len(states)
        assert len(trans_eqs) == len(trans)
        assert hint_symbs <= symbols
        assert all(isinstance(s, frozenset) for s in hint_states)
        assert all(isinstance(p, FNode) for s in hint_states for p in s)
        assert all(isinstance(eq, dict) for eq in hint_eqs)
        assert all(isinstance(k, FNode) for eq in hint_eqs for k in eq)
        assert all(isinstance(v, FNode) for eq in hint_eqs for v in eq.values())
        assert all(not s.is_true() for state in states for s in state)
        assert all(not s.is_false() for state in states for s in state)
        assert all(not s.is_true() for state in hint_states for s in state)
        assert all(not s.is_false() for state in hint_states for s in state)
        assert all(not s.is_true() for t in trans for s in t)
        assert all(not s.is_false() for t in hint_trans for s in t)
        assert all(isinstance(s, frozenset) for s in hint_trans)
        assert all(isinstance(p, FNode) for s in hint_trans for p in s)
        assert len(hint_states) == len(states)
        assert len(hint_trans) == len(trans)
        assert len(hint_eqs) == len(trans_eqs)
        assert all(len(t_eqs.keys() & h_eqs.keys()) == 0
                   for t_eqs, h_eqs in zip(trans_eqs, hint_eqs))

        self.env = env
        self.mgr = env.formula_manager
        self.totime = totime
        self.cn = cn
        self._src_idx = src_idx
        self._dst_idx = dst_idx
        self.states: List[Union[Set[FNode], FrozenSet[FNode]]] = \
            [set(state) for state in states]
        self.assigns = conc_assigns
        self._x_hint_symbs = frozenset(symb_to_next(self.mgr, s)
                                       for s in hint_symbs)
        get_free_vars = self.env.fvo.walk
        # avoid conflicts between hint and abst_trans.
        for idx in range(len(trans_eqs)):
            ts = trans[idx]
            eqs = trans_eqs[idx]
            hint_ts = hint_trans[idx]
            h_eqs = hint_eqs[idx]
            # rewrite ts to remove hint symbols for which we have an equality.
            if len(hint_eqs) > 0:
                _ts = set()
                for pred in ts:
                    pred = self.cn(self.simpl(self.subst(pred, h_eqs)))
                    assert not pred.is_false()
                    if not pred.is_true():
                        if all(symb_is_curr(s)
                               for s in get_free_vars(pred)):
                            self.states[idx].add(pred)
                        else:
                            _ts.add(pred)
                ts = frozenset(_ts)
                trans[idx] = ts

            if len(hint_ts) > 0 and (len(ts) > 0 or len(eqs) > 0):
                h_state = set()
                trans_symbs = (eqs.keys() & h_eqs.keys()) | frozenset(
                    chain.from_iterable(get_free_vars(t) & h_eqs.keys()
                                        for t in ts))
                _ts = set(ts)
                _hint_ts = set()
                for hint_t in hint_ts:
                    if get_free_vars(hint_t) & trans_symbs:
                        _ts.add(hint_t)
                    else:
                        _hint_ts.add(hint_t)
                trans[idx] = frozenset(_ts)
                hint_trans[idx] = frozenset(_hint_ts)
                x_idx = idx + 1 % len(self.states)
                h_state = set()
                trans_symbs = frozenset(symb_to_curr(s) for s in trans_symbs)
                for pred in hint_states[x_idx]:
                    if get_free_vars(pred) & trans_symbs:
                        self.states[x_idx].add(pred)
                    else:
                        h_state.add(pred)
                hint_states[x_idx] = frozenset(h_state)

        self.trans_eqs = trans_eqs
        self.hint_states = [set(state) for state in hint_states]
        self.hint_eqs = hint_eqs
        self.hint_trans = hint_trans
        self.last_ineqs: List[FNode] = []
        self.trans = trans
        self.conc_symbs = frozenset(ExprAtTime.symb_untime(self.mgr, s)
                                    for s in conc_assigns[0])
        assert all(self.conc_symbs ==
                   frozenset(ExprAtTime.symb_untime(self.mgr, s)
                             for s in assign)
                   for assign in conc_assigns)
        assert len(symbols & self.conc_symbs) == 0
        self._r_symbs = frozenset(s for s in symbols
                                  if s.symbol_type().is_real_type())
        self._i_symbs = frozenset(s for s in symbols
                                  if s.symbol_type().is_int_type())
        assert len(self._r_symbs) + len(self._i_symbs) > 0
        assert (self._r_symbs | self._i_symbs) == symbols

        zero = self.mgr.Real(0) if self.real_symbs else self.mgr.Int(0)
        self._params = set()
        self._ineqs = []
        for _ in range(num_ineqs):
            expr, params = self._linear_comb(self.symbs_to_same_type)
            self._params.update(params)
            assert all(p in self.mgr.get_all_symbols() for p in self._params)
            self._ineqs.append(self.cn(self.mgr.LE(expr, zero)))

    @property
    def first(self) -> int:
        return self._src_idx

    @property
    def last(self) -> int:
        return self._dst_idx

    @property
    def first_ineqs(self) -> List[FNode]:
        assert all(isinstance(ineq, FNode) for ineq in self._ineqs)
        return self._ineqs

    @property
    def parameters(self) -> FrozenSet[FNode]:
        assert all(p in self.mgr.get_all_symbols() for p in self._params)
        return frozenset(self._params)

    @property
    def all_symbs(self) -> FrozenSet[FNode]:
        return self.symbs | self.conc_symbs

    @property
    def symbs_to_real(self) -> FrozenSet[FNode]:
        return frozenset(self.mgr.ToReal(s)
                         for s in self.int_symbs) | self.real_symbs

    @property
    def symbs_to_same_type(self) -> FrozenSet[FNode]:
        if self.real_symbs:
            return self.symbs_to_real
        return self.int_symbs

    @property
    def symbs(self) -> FrozenSet[FNode]:
        return self.int_symbs | self.real_symbs

    @property
    def int_symbs(self) -> FrozenSet[FNode]:
        return self._i_symbs

    @property
    def real_symbs(self) -> FrozenSet[FNode]:
        return self._r_symbs

    @property
    def constraints(self) -> Iterator[FNode]:
        """Return iterable of Exist-Forall quantified constraints"""
        self.states = [frozenset(state) for state in self.states]
        yield from (self.simpl(self.mgr.Implies(self.mgr.And(lhs),
                                                self.mgr.And(rhs)))
                    for lhs, rhs in self._get_constr())

    @property
    def implications(self) -> Iterator[Tuple[FrozenSet[FNode],
                                             FrozenSet[FNode]]]:
        """Return pairs of implications [lhs] -> [rhs]

        lhs is purely conjunctive and rhs is purely disjunctive.
        """
        mgr = self.env.formula_manager
        self.states = [frozenset(state) for state in self.states]
        for lhs, rhs in self._get_constr():
            assert isinstance(lhs, frozenset)
            assert isinstance(rhs, frozenset)
            assert all(isinstance(l, FNode) for l in lhs)
            assert all(isinstance(r, FNode) for r in rhs)
            assert all(l in mgr.formulae.values() for l in lhs)
            assert all(r in mgr.formulae.values() for r in rhs)
            assert all(not l.is_false() for l in lhs)
            assert all(r in mgr.formulae.values() for r in rhs)
            assert all(not r.is_true() for r in rhs)
            assert all(not r.is_false() for r in rhs)
            assert all(r not in lhs for r in rhs)
            # elements of lhs purely conjunctive
            # elements of rhs purely disjunctive
            for r in (atm for it in rhs
                      for atm in self.split_eq(it)
                      if atm not in lhs):
                assert isinstance(r, FNode)
                yield lhs, frozenset([r])

    def strengthen_state(self, idx: int, *args) -> None:
        assert all(self.cn(s) == s for s in self.states[idx])
        assert isinstance(self.states[idx], set)
        self.states[idx].update(args)

        assert all(isinstance(a, FNode) for a in self.states[idx])
        assert all(self.cn(s) == s for s in self.states[idx])

    def strengthen_hint_state(self, idx: int, *args) -> None:
        assert all(self.cn(s) == s for s in self.hint_states[idx])
        assert isinstance(self.hint_states[idx], set)
        self.hint_states[idx].update(args)

        assert all(isinstance(a, FNode) for a in self.hint_states[idx])
        assert all(self.cn(s) == s for s in self.hint_states[idx])

    def simpl(self, formula: FNode) -> FNode:
        assert formula in self.mgr.formulae.values(), formula
        return self.env.simplifier.simplify(formula)

    def subst(self, formula: FNode, subs: Dict[FNode, FNode]) -> FNode:
        assert formula in self.mgr.formulae.values(), formula
        return self.env.substituter.substitute(formula, subs)

    def not_rel(self, rel: FNode) -> FNode:
        return not_rel(self.env, rel)

    def split_eq(self, fm: FNode) -> List[FNode]:
        assert isinstance(fm, FNode)
        if fm.is_equals():
            ge = self.mgr.GE(fm.arg(0), fm.arg(1))
            le = self.mgr.LE(fm.arg(0), fm.arg(1))
            return [ge, le]
        assert fm.is_constant() or fm.is_le() or fm.is_lt()
        return [fm]

    def cfg(self, model) -> list:
        res = []
        for idx in range(len(self.states[:-1])):
            res.append((self.first + idx + 1, None))
        return res

    def _new_symb(self, base: str, s_type) -> FNode:
        """Return fresh symbol of the given type"""
        assert s_type in {types.BOOL, types.INT, types.REAL}
        assert base is not None
        assert len(f"{Funnel.PREF}") > 0
        return new_symb(self.mgr, f"{Funnel.PREF}{base}", s_type)

    def _linear_comb(self, symbs: FrozenSet[FNode],
                     idx: Optional[int] = None) -> Tuple[FNode, List[FNode]]:
        """Return FNode expr representing linear combination of symbs and
        list of parameters"""
        return linear_comb(self.env, symbs, f"{Funnel.PREF}", idx, self.totime)

    def __init_subclass__(cls, *args, **kwargs):
        super().__init_subclass__(*args, **kwargs)
        assert hasattr(cls, "_get_constr")
        assert hasattr(cls, "describe")
        assert hasattr(cls, "backward_propagate")
        assert hasattr(cls, "backward_propagate_partial")


class ConcFunnel(Funnel):
    """Underapproximate each transition"""

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        assert len(self.trans) > 0
        assert len(self.trans) == self.last - self.first
        assert len(self.states) == len(self.trans) + 1

        get_free_vars = self.env.fvo.walk
        x_symbs = frozenset(symb_to_next(self.mgr, s) for s in self.symbs)
        self._u_trans = [{**eqs} for eqs in self.trans_eqs]
        # create parametric next-assignment for missing symbols.
        for u_eqs, h_eqs, h_trans in zip(self._u_trans, self.hint_eqs,
                                         self.hint_trans):
            # symbols already handled by other expressions.
            skip_x_symbs = frozenset(
                chain(u_eqs.keys(), h_eqs.keys(),
                      (self._x_hint_symbs & get_free_vars(h_t)
                       for h_t in h_trans)))
            for x_s in x_symbs - skip_x_symbs:
                assert x_s not in u_eqs
                assert symb_is_next(x_s)
                symbs = self.symbs_to_real if x_s.symbol_type().is_real_type() \
                    else self.int_symbs
                expr, params = self._linear_comb(symbs)
                self._params.update(params)
                assert all(p in self.mgr.get_all_symbols()
                           for p in self.parameters)
                u_eqs[x_s] = self.cn(expr)

    def _get_constr(self) -> Iterator[Tuple[FrozenSet[FNode],
                                            FrozenSet[FNode]]]:
        # state[0] & ineqs & hint_states[:i+1] & u_trans[:i] & hint_trans[:i] ->
        # trans[i-1] & state[i]
        lhs = set(self.totime(pred, self.first) for pred in
                  chain(self.states[0], self.hint_states[0], self.first_ineqs))
        for idx, (c_trans, h_trans, h_eqs, x_h_state) in enumerate(
                zip(self._u_trans, self.hint_trans, self.hint_eqs,
                    self.hint_states[1:])):
            assert all(k not in c_trans for k in h_eqs)
            x_idx = idx + 1
            c_time = idx + self.first
            x_time = c_time + 1
            lhs.update(self.totime(pred, c_time + 1) for pred in x_h_state)
            lhs.update(self.totime(self.mgr.Equals(symb, expr), c_time)
                       for symb, expr in chain(c_trans.items(), h_eqs.items()))
            lhs.update(self.totime(pred, c_time) for pred in h_trans)
            # substitute current and next concrete assignments in trans.
            assignments = {**self.assigns[idx],
                           **{symb_to_next(self.mgr, k): v
                              for k, v in self.assigns[x_idx].items()}}
            rhs = set(self.totime(self.simpl(self.subst(t, assignments)), c_time)
                      for t in self.trans[idx])
            if x_idx == len(self.states) - 1:
                rhs.update(self.totime(s, x_time) for s in self.last_ineqs)
            rhs.update(self.totime(s, x_time) for s in self.states[x_idx])
            rhs -= lhs
            assert all(isinstance(l, FNode) for l in lhs)
            assert all(not l.is_true() for l in lhs)
            assert all(not l.is_false() for l in lhs)
            assert all(isinstance(r, FNode) for r in rhs)
            assert all(not r.is_true() for r in rhs)
            assert all(not r.is_false() for r in rhs)
            if rhs:
                yield frozenset(lhs), frozenset(rhs)

    def backward_propagate(self, preds: Iterable[FNode],
                           h_preds: Iterable[FNode]) \
            -> Tuple[Tuple[FrozenSet[FNode], FrozenSet[FNode]],
                     Tuple[FrozenSet[FNode], FrozenSet[FNode]]]:
        """Push constraints on first state by applying transition equalities"""
        assert all(symb_is_curr(s) for p in preds
                   for s in self.env.fvo.walk(p))
        assert all(isinstance(s, set) for s in self.states)

        res = frozenset(chain(preds, self.last_ineqs))
        h_res = frozenset(h_preds)
        assert all(self.cn(s) == s for s in res)
        for c_state, h_state, c_eqs, h_trans in \
            reversed(list(zip(self.states[1:], self.hint_states[1:],
                              self._u_trans, self.hint_eqs))):
            eqs = {**c_eqs, **h_trans}
            # No assign loops: stricter than required, check 2 steps only.
            assert all(self.env.fvo.walk(v) <= self.symbs or
                       all(s not in eqs or eqs[s] <= self.symbs
                           for s in self.env.fvo.walk(v) - self.symbs)
                       for v in eqs.values())
            res = frozenset(self.cn(self.simpl(self.subst(to_next(self.mgr,
                                                                  pred,
                                                                  self.symbs),
                                                          eqs)))
                            for pred in chain(res, c_state)
                            if not pred.is_true())
            c_state.clear()

            h_res = frozenset(self.cn(self.simpl(self.subst(to_next(self.mgr,
                                                                    pred,
                                                                    self.symbs),
                                                            eqs)))
                              for pred in chain(h_res, h_state)
                              if not pred.is_true())
            h_state.clear()
        assert all(symb_is_curr(s) for p in res
                   for s in self.env.fvo.walk(p))
        assert all(self.cn(s) == s for s in res)
        assert all(not s.is_true() for s in res)
        assert all(symb_is_curr(s) for p in h_res
                   for s in self.env.fvo.walk(p))
        assert all(self.cn(s) == s for s in h_res)
        assert all(not s.is_true() for s in h_res)
        return (res, h_res), (frozenset(), frozenset())

    def backward_propagate_partial(self, preds: Iterable[FNode],
                                   h_preds: Iterable[FNode]) \
            -> Tuple[Tuple[FrozenSet[FNode], FrozenSet[FNode]],
                     Tuple[FrozenSet[FNode], FrozenSet[FNode]]]:
        assert all(symb_is_curr(s) for p in preds
                   for s in self.env.fvo.walk(p))
        assert all(symb_is_curr(s) for p in h_preds
                   for s in self.env.fvo.walk(p))
        assert all(isinstance(s, set) for s in self.states)
        assert all(isinstance(s, set) for s in self.hint_states)
        get_free_vars = self.env.fvo.walk
        res = frozenset(chain(preds, self.last_ineqs))
        h_res = frozenset(h_preds)
        for c_state, h_state, c_eqs, h_eqs in \
            reversed(list(zip(self.states[1:], self.hint_states[1:],
                              self.trans_eqs, self.hint_eqs))):
            assert all(k not in h_eqs for k in c_eqs)
            eqs = {**c_eqs, **h_eqs}
            # No assign loops: stricter than required, check 2 steps only.
            assert all(self.env.fvo.walk(v) <= self.symbs or
                       all(s not in eqs or eqs[s] <= self.symbs
                           for s in self.env.fvo.walk(v) - self.symbs)
                       for v in eqs.values())
            keys = frozenset(eqs.keys())
            c_preds = res | c_state
            c_state.clear()
            res = set()
            for p in c_preds:
                assert not p.is_true()
                x_p = to_next(self.mgr, p, self.symbs)
                if get_free_vars(x_p) <= keys:
                    p = self.cn(self.simpl(self.subst(x_p, eqs)))
                    if not p.is_true():
                        res.add(p)
                else:
                    c_state.add(p)

            c_preds = h_res | h_state
            h_state.clear()
            h_res = set()
            for p in c_preds:
                assert not p.is_false()
                assert not p.is_true()
                x_p = to_next(self.mgr, p, self.symbs)
                if get_free_vars(x_p) <= keys:
                    p = self.cn(self.simpl(self.subst(x_p, eqs)))
                    assert not p.is_false()
                    if not p.is_true():
                        h_res.add(p)
                else:
                    h_state.add(p)
        assert all(symb_is_curr(s) for p in res for s in get_free_vars(p))
        assert all(symb_is_curr(s) for p in h_res for s in get_free_vars(p))
        assert all(self.cn(p) == p for p in res)
        assert all(self.cn(p) == p for s in h_res)
        assert all(not p.is_true() for p in res)
        assert all(not p.is_true() for p in h_res)
        return (frozenset(res), frozenset(h_res)), (frozenset(), frozenset())

    def describe(self, param2val: Dict[FNode, FNode], indent: str,
                 buf: StringIO) -> None:
        assert isinstance(param2val, dict)
        assert isinstance(indent, str)
        assert isinstance(buf, StringIO)
        assert all(p in param2val for p in self.parameters)

        serialize = self.env.serializer.serialize
        ineqs = [self.simpl(self.subst(ineq, param2val))
                 for ineq in self.first_ineqs]
        eqs = [{u_s: self.simpl(self.subst(u_e, param2val))
                for u_s, u_e in trans.items()}
               for trans in self._u_trans]
        for c_time in range(self.first, self.last):
            idx = c_time - self.first
            buf.write(f"{indent}State {c_time}\n")
            for s, val in self.assigns[idx].items():
                buf.write(f"{indent}\t{serialize(s)} = {serialize(val)}\n")
            for s in self.states[idx]:
                buf.write(f"{indent}\t{serialize(self.simpl(self.subst(s, param2val)))}\n")
            for s in self.hint_states[idx]:
                buf.write(f"{indent}\t{serialize(s)}\t(hint)\n")
            if idx == 0:
                for ineq in ineqs:
                    buf.write(f"{indent}\t{serialize(ineq)}\n")
            buf.write(f"{indent}Trans {c_time} -- {c_time + 1}\n")
            for s, expr in eqs[idx].items():
                buf.write(f"{indent}\t{serialize(s)} = {serialize(expr)}\n")
            for s, expr in self.hint_eqs[idx].items():
                buf.write(f"{indent}\t{serialize(s)} = {serialize(expr)}\t(hint)\n")
            for t in self.hint_trans[idx]:
                buf.write(f"{indent}\t{serialize(t)}\t(hint)\n")

    def to_smv(self, model, state_var, buf, expr_print) -> None:
        assert len(self.assigns) == len(self.hint_states)

        eqs = [{u_s: self.simpl(self.subst(u_e, model))
                for u_s, u_e in trans.items()}
               for trans in self._u_trans]
        assert len(self.assigns) == len(eqs) + 1
        assert len(eqs) == len(self.hint_eqs)
        assert len(eqs) == len(self.hint_trans)

        buf.write("\n-- ConcFunnel\n")
        for idx, (trans, h_eqs, h_trans, x_h_state) in enumerate(
                zip(eqs, self.hint_eqs, self.hint_trans, self.hint_states[1:])):
            c_time = idx + self.first
            x_time = c_time + 1
            trans = [self.mgr.Equals(k, v)
                     for k, v in chain(trans.items(),
                                       h_eqs.items())]
            trans.extend(h_trans)
            trans.extend(to_next(self.mgr, pred, self.all_symbs)
                         for pred in x_h_state)
            buf.write(f"  -- transition from {c_time} to {x_time}\n")
            buf.write(f"  TRANS ({state_var} = {c_time} & "
                      f"next({state_var}) = {x_time}) ->\n    (\n     ")
            expr_print.printer(self.mgr.And(trans))
            buf.write("\n    );\n")

        buf.write("INVARSPEC NAME "
                  f"CFUN{self.first}_STATE_{self.first} := "
                  f"({state_var} = {self.first} & next({state_var}) = "
                  f"{self.first + 1}) -> ")
        invar = list(self.first_ineqs) + list(self.states[0])
        expr_print.printer(self.simpl(self.subst(self.mgr.And(invar), model)))
        buf.write(";\n")

        for idx, s in enumerate(self.states[1:]):
            s_idx = idx + 1 + self.first
            buf.write(f"INVARSPEC NAME CFUN{self.first}_STATE_{s_idx} := "
                      f"{state_var} = {s_idx} -> ")
            expr_print.printer(self.simpl(self.subst(self.mgr.And(s), model)))
            buf.write(";\n")
        buf.write("\n")


class RFFunnel(Funnel):
    """Ranked loop
    Repeat first -- last until ranking function,
    Finally last and not ranking funciton.
    """

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        assert len(self.trans) == len(self.states)
        assert len(self.trans) >= 1
        assert len(self.trans) == self.last - self.first + 1

        get_free_vars = self.env.fvo.walk
        self._rf_expr, params = \
            self._linear_comb(self.symbs_to_real)
        self._rf_expr = self.cn(self._rf_expr)
        rf_type = self.env.stc.get_type(self._rf_expr)
        self._rf_zero = self.mgr.Real(0) if rf_type.is_real_type() \
            else self.mgr.Int(0)
        self._rf_pred = self.cn(self.mgr.GT(self._rf_expr, self._rf_zero))
        self._params.update(params)
        assert all(p in self.mgr.get_all_symbols() for p in self._params)
        self._delta = self._new_symb("_d", rf_type)
        self._params.add(self._delta)

        assert len(self.last_ineqs) == 0
        self.last_ineqs.append(self.cn(self.not_rel(self._rf_pred)))
        x_symbs = frozenset(symb_to_next(self.mgr, s) for s in self.symbs)
        self._u_trans = [{**eqs} for eqs in self.trans_eqs]
        # create parametric next-assignment for missing symbols.
        for u_eqs, h_eqs, h_trans in zip(self._u_trans, self.hint_eqs,
                                         self.hint_trans):
            # symbols already handled by other expressions.
            skip_x_symbs = frozenset(
                chain(u_eqs.keys(), h_eqs.keys(),
                      (self.x_hint_symbs & get_free_vars(h_t)
                       for h_t in h_trans)))
            for x_s in x_symbs - skip_x_symbs:
                assert x_s not in u_eqs
                assert symb_is_next(x_s)
                symbs = self.symbs_to_real if x_s.symbol_type().is_real_type() \
                    else self.int_symbs
                expr, params = self._linear_comb(symbs)
                self._params.update(params)
                assert all(p in self.mgr.get_all_symbols()
                           for p in self.parameters)
                u_eqs[x_s] = self.cn(expr)

    def _get_constr(self) -> Iterator[Tuple[FrozenSet[FNode], FrozenSet[FNode]]]:
        assert self.first + len(self._u_trans) == self.last + 1
        assert len(self._u_trans) == len(self.states)
        # delta >= 0
        yield (frozenset([self.mgr.TRUE()]),
               frozenset([self.mgr.GE(self._delta, self._rf_zero)]))

        # ineqs & state[0] & hint_states[:i+1] & u_trans[:i] & hint_trans[:i] ->
        # trans[i-1] & state[i]
        lhs = set(self.totime(pred, self.first) for pred in
                  chain(self.states[0], self.hint_states[0], self.first_ineqs))
        assert all(not l.is_true() for l in lhs)
        for idx, (c_trans, h_trans, h_eqs, x_h_state) in enumerate(
                zip(self._u_trans[:-1], self.hint_trans[:-1], self.hint_eqs[:-1],
                    self.hint_states[1:-1])):
            assert all(k not in c_trans for k in h_eqs)
            x_idx = idx + 1
            c_time = idx + self.first
            x_time = c_time + 1
            lhs.update(self.totime(pred, c_time + 1) for pred in x_h_state)
            lhs.update(self.totime(self.mgr.Equals(symb, expr), c_time)
                       for symb, expr in chain(c_trans.items(), h_eqs.items()))
            lhs.update(self.totime(pred, c_time) for pred in h_trans)
            # substitute current and next concrete assignments in trans.
            assignments = {**self.assigns[idx],
                           **{symb_to_next(self.mgr, k): v
                              for k, v in self.assigns[x_idx].items()}}
            rhs = set(self.totime(self.simpl(self.subst(t, assignments)), c_time)
                      for t in self.trans[idx])
            rhs.update(self.totime(s, x_time) for s in self.states[x_idx])
            rhs -= lhs
            assert all(isinstance(l, FNode) for l in lhs)
            assert all(not l.is_true() for l in lhs)
            assert all(not l.is_false() for l in lhs)
            assert all(isinstance(r, FNode) for r in rhs)
            assert all(not r.is_true() for r in rhs)
            assert all(not r.is_false() for r in rhs)
            if rhs:
                yield frozenset(lhs), frozenset(rhs)

        c_time = self.last
        # first_ineqs & states & u_trans & h_trans & rf < 0 -> last_ineqs
        not_ranked = self.cn(self.totime(self.not_rel(self._rf_pred),
                                         c_time))
        assert not not_ranked.is_true()
        lhs.add(not_ranked)
        assert self.last_ineqs[0] == self.cn(self.not_rel(self._rf_pred))
        rhs = set(self.totime(l_ineq, c_time)
                  for l_ineq in self.last_ineqs[1:])
        rhs -= lhs
        assert all(isinstance(l, FNode) for l in lhs)
        assert all(not l.is_true() for l in lhs)
        assert all(not l.is_false() for l in lhs)
        assert all(isinstance(r, FNode) for r in rhs)
        assert all(not r.is_true() for r in rhs)
        assert all(not r.is_false() for r in rhs)
        if rhs:
            yield frozenset(lhs), frozenset(rhs)

        # ineqs & states & u_trans & h_trans & rf >= 0 & last_t ->
        # trans & state[0]' & ineqs'
        lhs.remove(not_ranked)
        assert not_ranked not in lhs
        x_time = c_time + 1
        # rf >= 0
        _lhs = set(lhs)
        assert _lhs is not lhs
        _lhs.add(self.totime(self._rf_pred, c_time))
        # last_t
        _lhs.update(self.totime(self.mgr.Equals(u_symb, u_expr), c_time)
                    for u_symb, u_expr in self._u_trans[-1].items())
        # trans
        last_t_assign = {**self.assigns[-1],
                         **{symb_to_next(self.mgr, k): v
                            for k, v in self.assigns[0].items()}}
        rhs = set(self.totime(self.simpl(self.subst(t, last_t_assign)),
                              c_time)
                  for t in self.trans[-1])
        # ineqs' & state[0]'
        rhs.update(self.totime(pred, x_time)
                   for pred in chain(self.first_ineqs, self.states[0]))
        rhs -= _lhs
        assert all(isinstance(l, FNode) for l in _lhs)
        assert all(not l.is_true() for l in _lhs)
        assert all(not l.is_false() for l in _lhs)
        assert all(isinstance(r, FNode) for r in rhs)
        assert all(not r.is_true() for r in rhs)
        assert all(not r.is_false() for r in rhs)
        if rhs:
            yield frozenset(_lhs), frozenset(rhs)
        del _lhs

        # rf >= 0 & last_t & state[0] & first_ineqs & u_trans & h_trans ->
        # decrease(rf)
        start_t = self.last + 3  # cannot use self.first - 1 (first might be 0)
        end_t = self.first
        # rf >= 0
        lhs.add(self.totime(self._rf_pred, start_t, x_idx=end_t))
        # last_t: u_trans[-1] & hint_eqs[-1] & hint_trans[-1]
        lhs.update(self.totime(self.mgr.Equals(symb, expr), start_t,
                               x_idx=end_t)
                   for symb, expr in chain(self._u_trans[-1].items(),
                                           self.hint_eqs[-1].items()))
        lhs.update(self.totime(pred, start_t, x_idx=end_t)
                   for pred in self.hint_trans[-1])

        dec_rf = self.mgr.Minus(self.totime(self._rf_expr, start_t,
                                            x_idx=end_t),
                                self._delta)
        dec_rf = self.mgr.LT(self.totime(self._rf_expr, self.last), dec_rf)
        assert isinstance(dec_rf, FNode)
        assert all(isinstance(l, FNode) for l in lhs)
        assert all(not l.is_true() for l in lhs)
        assert all(not l.is_false() for l in lhs)
        if dec_rf not in lhs:
            yield frozenset(lhs), frozenset([dec_rf])

    def backward_propagate(self,
                           preds: Iterable[FNode],
                           h_preds: Iterable[FNode]) \
            -> Tuple[Tuple[FrozenSet[FNode], FrozenSet[FNode]],
                     Tuple[FrozenSet[FNode], FrozenSet[FNode]]]:
        """Push constraints on first state via transition relation"""
        assert len(self.trans) == len(self._u_trans)
        assert len(self._u_trans) == len(self.hint_eqs)
        assert len(self.hint_eqs) == len(self.hint_trans)
        assert len(self.states) == len(self._u_trans)
        assert len(self.hint_states) == len(self.states)

        assert all(isinstance(s, set) for s in self.states)
        assert all(isinstance(s, set) for s in self.hint_states)

        res, keep = self._split_inductive_preds(preds)
        h_res, h_keep = self._split_inductive_preds(h_preds)

        for state, h_state, eqs, h_eqs in \
            reversed(list(zip(self.states[1:], self.hint_states[1:],
                              self._u_trans, self.hint_eqs))):
            all_eqs = {**eqs, **h_eqs}
            # No assign loops: stricter than required, check 2 steps only.
            assert all(self.env.fvo.walk(v) <= self.symbs or
                       all(s not in eqs or eqs[s] <= self.symbs
                           for s in self.env.fvo.walk(v) - self.symbs)
                       for v in eqs.values())
            res = frozenset(self.cn(self.simpl(self.subst(to_next(self.mgr,
                                                                  pred,
                                                                  self.symbs),
                                                          all_eqs)))
                            for pred in chain(res, state)
                            if not pred.is_true())
            state.clear()

            h_res = frozenset(self.cn(self.simpl(self.subst(to_next(self.mgr,
                                                                    pred,
                                                                    self.symbs),
                                                            all_eqs)))
                              for pred in chain(h_res, h_state)
                              if not pred.is_true())
            h_state.clear()

        assert isinstance(res, frozenset)
        assert all(symb_is_curr(s) for p in res
                   for s in self.env.fvo.walk(p))
        assert all(self.cn(p) == p for p in res)
        assert all(not p.is_false() for p in res)
        assert all(not p.is_true() for p in res)
        assert isinstance(keep, frozenset)
        assert all(self.cn(p) == p for p in keep)
        assert all(not p.is_false() for p in keep)
        assert all(not p.is_true() for p in keep)
        assert all(symb_is_curr(s) for p in h_res
                   for s in self.env.fvo.walk(p))
        assert isinstance(h_res, frozenset)
        assert all(self.cn(p) == p for p in h_res)
        assert all(not p.is_false() for p in h_res)
        assert all(not p.is_true() for p in h_res)
        assert isinstance(h_keep, frozenset)
        assert all(self.cn(p) == p for p in h_keep)
        assert all(not p.is_false() for p in h_keep)
        assert all(not p.is_true() for p in h_keep)
        return (res, h_res), (keep, h_keep)

    def backward_propagate_partial(self, preds: Iterable[FNode],
                                   h_preds: Iterable[FNode]) \
            -> Tuple[Tuple[FrozenSet[FNode], FrozenSet[FNode]],
                     Tuple[FrozenSet[FNode], FrozenSet[FNode]]]:
        """Push constraints on first state via transition relation"""
        assert len(self.trans) == len(self._u_trans)
        assert len(self._u_trans) == len(self.hint_eqs)
        assert len(self.hint_eqs) == len(self.hint_trans)
        assert len(self.states) == len(self._u_trans)
        assert len(self.hint_states) == len(self.states)

        assert all(isinstance(s, set) for s in self.states)
        assert all(isinstance(s, set) for s in self.hint_states)

        get_free_vars = self.env.fvo.walk
        res, keep = self._split_inductive_preds(preds)
        h_res, h_keep = self._split_inductive_preds(h_preds)

        for state, h_state, c_eqs, h_eqs in \
            reversed(list(zip(self.states[1:], self.hint_states[1:],
                              self.trans_eqs, self.hint_eqs))):
            assert all(k not in h_eqs for k in c_eqs)
            eqs = {**c_eqs, **h_eqs}
            # No assign loops: stricter than required, check 2 steps only.
            assert all(self.env.fvo.walk(v) <= self.symbs or
                       all(s not in eqs or eqs[s] <= self.symbs
                           for s in self.env.fvo.walk(v) - self.symbs)
                       for v in eqs.values())
            keys = frozenset(eqs.keys())
            assert keys <= frozenset(symb_to_next(self.env.formula_manager, s)
                                     for s in self.symbs)
            c_preds = res | state
            state.clear()
            res = set()
            for p in c_preds:
                assert not p.is_false()
                assert not p.is_true()
                x_p = to_next(self.mgr, p, self.symbs)
                if get_free_vars(x_p) <= keys:
                    p = self.cn(self.simpl(self.subst(x_p, eqs)))
                    assert not p.is_false()
                    if not p.is_true():
                        res.add(p)
                else:
                    state.add(p)
            c_preds = h_res | h_state
            h_state.clear()
            h_res = set()
            for p in c_preds:
                assert not p.is_false()
                assert not p.is_true()
                x_p = to_next(self.mgr, p, self.symbs)
                if get_free_vars(x_p) <= keys:
                    p = self.cn(self.simpl(self.subst(x_p, eqs)))
                    assert not p.is_false()
                    if not p.is_true():
                        h_res.add(p)
                else:
                    h_state.add(p)

        assert all(symb_is_curr(s) for p in res for s in get_free_vars(p))
        assert all(self.cn(p) == p for p in res)
        assert all(not p.is_true() for p in res)
        assert all(not p.is_false() for p in res)
        assert all(symb_is_curr(s) for p in h_res for s in get_free_vars(p))
        assert all(self.cn(p) == p for p in h_res)
        assert all(not p.is_true() for p in h_res)
        assert all(not p.is_false() for p in h_res)
        assert all(symb_is_curr(s) for p in keep for s in get_free_vars(p))
        assert all(self.cn(p) == p for p in keep)
        assert all(not p.is_true() for p in keep)
        assert all(not p.is_false() for p in keep)
        assert all(symb_is_curr(s) for p in h_keep for s in get_free_vars(p))
        assert all(self.cn(p) == p for p in h_keep)
        assert all(not p.is_true() for p in h_keep)
        assert all(not p.is_false() for p in h_keep)
        return (frozenset(res), frozenset(h_res)), (keep, h_keep)

    def describe(self, param2val: Dict[FNode, FNode], indent: str,
                 buf: StringIO) -> None:
        assert isinstance(param2val, dict)
        assert isinstance(indent, str)
        assert isinstance(buf, StringIO)
        assert all(p in param2val for p in self.parameters)

        serialize = self.env.serializer.serialize
        ineqs = filter(lambda x: not x.is_true(),
                       (self.simpl(self.subst(ineq, param2val))
                        for ineq in self.first_ineqs))
        eqs = [{u_s: self.simpl(self.subst(u_e, param2val))
                for u_s, u_e in trans.items()}
               for trans in self._u_trans]
        rf_ineq = self.simpl(self.subst(self._rf_pred, param2val))
        buf.write(f"{indent}Do states {self.first}..{self.last} while {serialize(rf_ineq)}\n")
        for c_time in range(self.first, self.last + 1):
            idx = c_time - self.first
            buf.write(f"{indent}State {c_time}\n")
            for s, val in self.assigns[idx].items():
                buf.write(f"{indent}\t{serialize(s)} = {serialize(val)}\n")
            for s in self.states[idx]:
                buf.write(f"{indent}\t"
                          f"{serialize(self.simpl(self.subst(s, param2val)))}\n")
            for s in self.hint_states[idx]:
                buf.write(f"{indent}\t{serialize(s)}\t(hint)\n")
            if idx == 0:
                for ineq in ineqs:
                    buf.write(f"{indent}\t{serialize(ineq)}\n")
            buf.write(f"{indent}Trans {c_time} -- "
                      f"{c_time + 1 if c_time < self.last else self.first}\n")
            for s, expr in eqs[idx].items():
                buf.write(f"{indent}\t{serialize(s)} : {serialize(expr)}\t\n")
            for s, expr in self.hint_eqs[idx].items():
                buf.write(f"{indent}\t{serialize(s)} : {serialize(expr)}\t(hint)\n")
            for pred in self.hint_trans[idx]:
                buf.write(f"{indent}\t{serialize(pred)}\t(hint)\n")
        buf.write(f"{indent}End do-while\n")

    def cfg(self, model) -> List[Tuple[int, Union[FrozenSet[FNode], FNode]]]:
        res = [(self.first + idx + 1, frozenset())
               for idx in range(len(self.states) - 1)]
        rf_ineq = self.simpl(self.subst(self._rf_pred, model))
        res.append((self.first, rf_ineq))
        return res

    def to_smv(self, model, state_var, buf, expr_print) -> None:
        assert len(self.assigns) == len(self.hint_states)

        eqs = [{u_s: self.simpl(self.subst(u_e, model))
                for u_s, u_e in trans.items()}
               for trans in self._u_trans]
        assert len(self.assigns) == len(eqs)
        assert len(self.assigns) == len(self.hint_eqs)
        assert len(self.assigns) == len(self.hint_trans)

        buf.write("\n-- RFFunnel\n")
        for idx, (trans, h_eqs, h_trans, x_h_state) in enumerate(
                zip(eqs[:-1], self.hint_eqs[:-1], self.hint_trans[:-1],
                    self.hint_states[1:])):
            c_time = idx + self.first
            x_time = c_time + 1
            trans = [self.mgr.Equals(k, v)
                     for k, v in chain(trans.items(), h_eqs.items())]
            trans.extend(h_trans)
            trans.extend(to_next(self.mgr, pred, self.all_symbs)
                         for pred in x_h_state)
            buf.write(f"  -- transition from {c_time} to {x_time}\n")
            buf.write(f"  TRANS ({state_var} = {c_time} & "
                      f"next({state_var}) = {x_time}) ->\n    (\n     ")
            expr_print.printer(self.mgr.And(trans))
            buf.write("\n    );\n")
        trans = [self.mgr.Equals(k, v)
                 for k, v in chain(eqs[-1].items(),
                                   self.hint_eqs[-1].items())]
        trans.extend(self.hint_trans[-1])
        trans.extend(to_next(self.mgr, pred, self.all_symbs)
                     for pred in self.hint_states[0])
        c_time = self.last
        x_time = self.first
        buf.write(f"  -- loop-back transition from {c_time} to {x_time}\n")
        buf.write(f"  TRANS ({state_var} = {c_time} & "
                  f"next({state_var}) = {x_time}) ->\n    (\n     ")
        expr_print.printer(self.mgr.And(trans))
        buf.write("\n    );\n")

        buf.write("INVARSPEC NAME "
                  f"RFFUN{self.first}_STATE_{self.first} := "
                  f"({state_var} = {self.first} & "
                  f"next({state_var}) = {self.first + 1}) -> ")
        invar = list(self.first_ineqs) + list(self.states[0])
        expr_print.printer(self.simpl(self.subst(self.mgr.And(invar), model)))
        buf.write(";\n")

        for idx, s in enumerate(self.states[1:]):
            s_idx = idx + 1 + self.first
            buf.write(f"INVARSPEC NAME RFFUN{self.first}_STATE_{s_idx} := "
                      f"{state_var} = {s_idx} -> ")
            expr_print.printer(self.simpl(self.subst(self.mgr.And(s), model)))
            buf.write(";\n")
        buf.write("INVARSPEC NAME "
                  f"RFFUN{self.first}_STATE_{self.last}_EXIT := "
                  f"({state_var} = {self.last} & "
                  f"next({state_var}) != {self.first}) -> ")
        expr_print.printer(self.simpl(self.subst(self.mgr.And(self.last_ineqs),
                                                 model)))
        buf.write(";\n\n")

    def _split_inductive_preds(self, preds: Iterable[FNode]) \
            -> Tuple[FrozenSet[FNode], FrozenSet[FNode]]:
        assert len(self.trans) == len(self._u_trans)
        assert len(self._u_trans) == len(self.hint_eqs)
        assert len(self.hint_eqs) == len(self.hint_trans)
        assert all(symb_is_curr(s) for p in preds
                   for s in self.env.fvo.walk(p))
        assert all(not p.is_true() for p in preds)
        assert all(not p.is_false() for p in preds)
        invar = set()
        not_invar = set()

        with MultiSolver(self.env, FunnelLoop.get_timeout()) as solver:
            for idx, (eqs, trans, h_eqs, h_trans) in enumerate(
                    zip(self._u_trans, self.trans,
                        self.hint_eqs, self.hint_trans)):
                for s, expr in chain(eqs.items(), h_eqs.items()):
                    assert not symb_is_curr(s)
                    solver.add_assertion(self.mgr.Equals(self.totime(s, idx),
                                                         self.totime(expr, idx)))
                for pred in chain(trans, h_trans):
                    solver.add_assertion(self.totime(pred, idx))
            assertions = solver.assertions
            end = len(self._u_trans)
            # check which predicates are preserved by backward transition.
            for p in preds:
                solver.push()
                solver.add_assertion(self.totime(p, end))
                solver.add_assertion(self.mgr.Not(self.totime(p, 0)))
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

        return frozenset(invar), frozenset(not_invar)
