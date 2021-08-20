from typing import Tuple, Union, Optional, List, Set, Dict, FrozenSet, Iterable
from itertools import chain
from collections import defaultdict

from pysmt.environment import Environment as PysmtEnv
from pysmt.formula import FormulaManager
from pysmt.fnode import FNode
from pysmt.exceptions import SolverReturnedUnknownResultError

from utils import log, default_key, symb_to_next, symb_to_curr, \
    symb_is_next, symb_is_curr, to_next, assign2fnode, assign2fnodes, \
    is_not_true
from expr_at_time import ExprAtTime
from canonize import Canonizer
from rewritings import TimesDistributor
from abstract_loops import BMC
from funnel import FunnelLoop, Funnel
from ranker import Ranker
from generalised_lasso import is_generalised_lasso
from ineq import eq2assign
from hint import Hint
from rankfun import RankFun
from multisolver import MultiSolver

_USE_EF = True
_USE_EF_RF = True
_RF_LEARN_EF = False
_FUN_LEARN_EF = False
_USE_MOTZKIN = True
_USE_MOTZKIN_RF = True
# _SYNTH_RF = True
_USE_GENERALISED_LASSO = False
_EXTRACT_CONST_SYMBS_TIMEOUT = 5
_LOG_LVL = 1


def set_use_ef(val: bool) -> None:
    global _USE_EF
    assert isinstance(val, bool)
    _USE_EF = val


def get_use_ef() -> bool:
    global _USE_EF
    return _USE_EF


def set_use_ef_rf(val: bool) -> None:
    global _USE_EF_RF
    assert isinstance(val, bool)
    _USE_EF_RF = val


def get_use_ef_rf() -> bool:
    global _USE_EF_RF
    return _USE_EF_RF


def set_rf_learn_ef(val: bool) -> None:
    global _RF_LEARN_EF
    assert isinstance(val, bool)
    _RF_LEARN_EF = val


def get_rf_learn_ef() -> bool:
    global _RF_LEARN_EF
    return _RF_LEARN_EF


def set_fun_learn_ef(val: bool) -> None:
    global _FUN_LEARN_EF
    assert isinstance(val, bool)
    _FUN_LEARN_EF = val


def get_fun_learn_ef() -> bool:
    global _FUN_LEARN_EF
    return _FUN_LEARN_EF


def set_use_motzkin(val: bool) -> None:
    global _USE_MOTZKIN
    assert isinstance(val, bool)
    _USE_MOTZKIN = val


def get_use_motzkin() -> bool:
    global _USE_MOTZKIN
    return _USE_MOTZKIN


def set_use_motzkin_rf(val: bool) -> None:
    global _USE_MOTZKIN_RF
    assert isinstance(val, bool)
    _USE_MOTZKIN_RF = val


def get_use_motzkin_rf() -> bool:
    global _USE_MOTZKIN_RF
    return _USE_MOTZKIN_RF


def get_use_rank_fun() -> bool:
    return get_use_ef_rf() or get_use_motzkin_rf()


def set_extract_const_symbs_timeout(val: int) -> None:
    global _EXTRACT_CONST_SYMBS_TIMEOUT
    _EXTRACT_CONST_SYMBS_TIMEOUT = val


def get_extract_const_symbs_timeout() -> int:
    global _EXTRACT_CONST_SYMBS_TIMEOUT
    return _EXTRACT_CONST_SYMBS_TIMEOUT

def set_use_generalised_lasso(val: bool) -> None:
    global _USE_GENERALISED_LASSO
    _USE_GENERALISED_LASSO = val


def get_use_generalised_lasso() -> bool:
    global _USE_GENERALISED_LASSO
    return _USE_GENERALISED_LASSO


def get_log_lvl() -> int:
    global _LOG_LVL
    return _LOG_LVL


def search_funnel_bmc(env: PysmtEnv, symbols: FrozenSet[FNode],
                      init: FNode, trans: FNode, fair: FNode,
                      all_hints: FrozenSet[Hint]) -> \
                      Tuple[Optional[list],
                            Optional[Union[FunnelLoop,
                                           list, frozenset]],
                            Optional[Union[dict, frozenset]]]:
    assert isinstance(env, PysmtEnv)
    assert isinstance(symbols, frozenset)
    assert isinstance(init, FNode)
    assert isinstance(trans, FNode)
    assert isinstance(fair, FNode)
    assert isinstance(all_hints, frozenset)
    assert all(isinstance(h, Hint) for h in all_hints)
    assert all(h.env == env for h in all_hints)

    mgr = env.formula_manager
    simpl = env.simplifier.simplify
    serialize = env.serializer.serialize
    init = simpl(init)
    trans = simpl(trans)
    fair = simpl(fair)
    totime = ExprAtTime(env=env)
    loop_gen = BMC(env, init, trans, fair, all_hints, symbols)
    for i, (trace, lback_idx, abst_path, hints) in \
            enumerate(loop_gen.gen_loops()):
        if trace is None:
            assert lback_idx is None
            assert abst_path is None
            assert hints is None
            # We might have skipped some trace, not a problem.
            continue

        assert isinstance(trace, list)
        assert all(isinstance(state, dict) for state in trace)
        assert all(s in mgr.get_all_symbols()
                   for state in trace for s in state.keys())
        assert all(v in mgr.formulae.values()
                   for state in trace for v in state.values())
        assert all(s in mgr.get_all_symbols()
                   for state in trace for v in state.values()
                   for s in env.fvo.walk(v))
        assert all(len(ExprAtTime.collect_times(mgr, k)) == 0
                   for state in trace for k in state)
        assert all(env.stc.walk(s) == env.stc.walk(v)
                   for state in trace for s, v in state.items())
        assert (abst_path is False and hints is False) or \
            (abst_path is not False and hints is not False)
        assert abst_path is False or isinstance(abst_path, tuple)
        assert abst_path is False or len(abst_path) == 2
        assert abst_path is False or isinstance(abst_path[0], list)
        assert abst_path is False or isinstance(abst_path[1], list)
        assert abst_path is False or len(abst_path[1]) == len(abst_path[0]) - 1
        assert abst_path is False or all(isinstance(abst_s, frozenset)
                                         for abst_s in abst_path[0])
        assert abst_path is False or all(isinstance(abst_t, frozenset)
                                         for abst_t in abst_path[1])
        assert abst_path is False or all(isinstance(s, FNode)
                                         for abst_s in abst_path[0]
                                         for s in abst_s)
        assert abst_path is False or all(isinstance(t, FNode)
                                         for abst_t in abst_path[1]
                                         for t in abst_t)
        assert abst_path is False or all(isinstance(s, FNode)
                                         for abst_s in abst_path[0]
                                         for s in abst_s)
        assert abst_path is False or all(isinstance(t, FNode)
                                         for abst_t in abst_path[1]
                                         for t in abst_t)
        assert abst_path is False or all(s in mgr.formulae.values()
                                         for abst_s in abst_path[0]
                                         for s in abst_s)
        assert abst_path is False or all(t in mgr.formulae.values()
                                         for abst_t in abst_path[1]
                                         for t in abst_t)
        assert hints is False or isinstance(hints, tuple)
        assert hints is False or len(hints) == 3
        assert hints is False or isinstance(hints[0], list)
        assert hints is False or isinstance(hints[1], list)
        assert hints is False or isinstance(hints[2], list)
        assert hints is False or all(isinstance(h, Hint) for h in hints[0])
        assert hints is False or all(h.env == env for h in hints[0])
        assert abst_path is False or len(hints[2]) == len(hints[1]) - 1
        assert abst_path is False or all(isinstance(hint_s, frozenset)
                                         for hint_s in hints[1])
        assert abst_path is False or all(isinstance(hint_t, frozenset)
                                         for hint_t in hints[2])
        assert abst_path is False or all(isinstance(s, FNode)
                                         for hint_s in hints[1]
                                         for s in hint_s)
        assert abst_path is False or all(isinstance(t, FNode)
                                         for hint_t in hints[2]
                                         for t in hint_t)
        assert abst_path is False or all(isinstance(s, FNode)
                                         for hint_s in hints[1]
                                         for s in hint_s)
        assert abst_path is False or all(isinstance(t, FNode)
                                         for hint_t in hints[2]
                                         for t in hint_t)
        assert abst_path is False or all(s in mgr.formulae.values()
                                         for hint_s in hints[1]
                                         for s in hint_s)
        assert abst_path is False or all(t in mgr.formulae.values()
                                         for hint_t in hints[2]
                                         for t in hint_t)

        log(f"\n\tBMC: found trace {i}, len {len(trace)}, lback {lback_idx}",
            get_log_lvl())
        for j, state in enumerate(trace):
            log(f"\t    State {j} of trace {i}", get_log_lvl())
            log("\n".join(f"\t      {serialize(k)} : {serialize(state[k])}"
                          for k in sorted(state.keys(), key=default_key)),
                get_log_lvl())
        log(f"\tEnd of trace {i}\n", get_log_lvl())

        if abst_path is False:
            assert hints is False
            return trace[:lback_idx], trace[lback_idx:], None

        is_rf, args = rf_or_funnel_from_trace(env, symbols, trace, abst_path,
                                              hints, fair, lback_idx, totime,
                                              trans)
        assert isinstance(is_rf, bool)
        assert is_rf or isinstance(args, tuple)
        assert is_rf or len(args) == 3

        if is_rf and args is not None:
            assert isinstance(args, RankFun)
            loop_gen.add_ranking_rel(args)
            # loop_gen.add_ranking_rels(args)

        if not is_rf and args[1] is not None:
            assert isinstance(args, tuple)
            assert args[0] is not None
            assert args[1] is not None
            # either NontermArg or generalised lasso.
            return args

    return None, None, None


def rf_or_funnel_from_trace(env: PysmtEnv,
                            _symbs: FrozenSet[FNode],
                            trace: List[Dict[FNode, FNode]],
                            abst_path: Tuple[List[FrozenSet[FNode]],
                                             List[FrozenSet[FNode]]],
                            hints: Tuple[List[Hint], List[FrozenSet[FNode]],
                                         List[FrozenSet[FNode]]],
                            fair: FNode, first: int,
                            totime: ExprAtTime,
                            orig_trans: FNode) \
        -> Union[Tuple[bool, List[Dict[FNode, FNode]],
                       FrozenSet[FNode], FrozenSet[FNode]],
                 Tuple[bool, Optional[RankFun]],
                 Tuple[bool, Tuple[List[Dict[FNode, FNode]],
                                   Funnel, Dict[FNode, FNode]]]]:
    assert isinstance(env, PysmtEnv)
    assert isinstance(_symbs, frozenset)
    assert all(isinstance(s, FNode) for s in _symbs)
    assert all(s in env.formula_manager.get_all_symbols() for s in _symbs)
    assert isinstance(trace, list)
    assert all(isinstance(state, dict) for state in trace)
    assert all(isinstance(k, FNode) for state in trace for k in state)
    assert all(isinstance(v, FNode) for state in trace for v in state.values())
    assert all(k in env.formula_manager.get_all_symbols()
               for state in trace for k in state)
    assert all(v in env.formula_manager.formulae.values()
               for state in trace for v in state.values())
    assert all(env.stc.walk(s) == env.stc.walk(v)
               for state in trace for s, v in state.items())
    assert isinstance(abst_path, tuple)
    assert len(abst_path) == 2
    assert isinstance(abst_path[0], list)
    assert isinstance(abst_path[1], list)
    assert len(abst_path[0]) + first == len(trace)
    assert len(abst_path[0]) == len(abst_path[1]) + 1
    assert all(isinstance(abst_s, frozenset) for abst_s in abst_path[0])
    assert all(isinstance(abst_t, frozenset) for abst_t in abst_path[1])
    assert all(isinstance(s, FNode) for abst_s in abst_path[0] for s in abst_s)
    assert all(isinstance(t, FNode) for abst_t in abst_path[1] for t in abst_t)
    assert all(s in env.formula_manager.formulae.values()
               for abst_s in abst_path[0] for s in abst_s)
    assert all(t in env.formula_manager.formulae.values()
               for abst_t in abst_path[1] for t in abst_t)
    assert all(s in env.formula_manager.get_all_symbols()
               for abst_s in abst_path[0] for c in abst_s
               for s in env.fvo.walk(c))
    assert all(s in env.formula_manager.get_all_symbols()
               for abst_t in abst_path[1] for t in abst_t
               for s in env.fvo.walk(t))
    assert isinstance(hints, tuple)
    assert len(hints) == 3
    assert all(isinstance(hints_el, list) for hints_el in hints)
    assert all(isinstance(h, Hint) for h in hints[0])
    assert all(h.env == env for h in hints[0])
    assert all(isinstance(it, frozenset) for hints_el in hints[1:]
               for it in hints_el)
    assert all(isinstance(s, FNode) for hints_el in hints[1:]
               for it in hints_el for s in it)
    assert all(s in env.formula_manager.formulae.values()
               for hints_el in hints[1:] for it in hints_el for s in it)
    assert all(s in env.formula_manager.get_all_symbols()
               for hints_el in hints[1:] for it in hints_el
               for el in it for s in env.fvo.walk(el))
    assert isinstance(fair, FNode)
    assert fair in env.formula_manager.formulae.values()
    assert isinstance(totime, ExprAtTime)
    assert isinstance(first, int)
    assert first >= 0
    assert first < len(trace)
    assert len(abst_path[1]) == len(hints[2])
    assert len(abst_path[0]) == len(hints[1])

    last = len(trace) - 1
    mgr = env.formula_manager
    serialize = env.serializer.serialize
    cn = Canonizer(env=env)
    td = TimesDistributor(env=env)

    if get_use_generalised_lasso():
        res, div_pos, div_neg = \
            is_generalised_lasso(env, trace[first:], _symbs,
                                 mgr.And(chain.from_iterable(chain(
                                     abst_path[0], abst_path[1],
                                     hints[1], hints[2]))),
                                 td)
        if res:
            return False, (trace[first:], div_pos, div_neg)

    _abst_states, _abst_trans = abst_path
    _hints, _hints_states, _hints_trans = hints
    # last state implies first state : safe to copy predicates.
    _abst_states[-1] = _abst_states[0] | _abst_states[-1]
    _hints_states[-1] = _hints_states[0] | _hints_states[-1]
    del abst_path
    del hints

    if __debug__:
        simpl = env.simplifier.simplify
        subst = env.substituter.substitute
        for idx, s in enumerate(_abst_states):
            for p in s:
                assert simpl(subst(p, trace[idx + first])).is_true()
        for idx, t in enumerate(_abst_trans):
            for p in t:
                p = subst(p, {symb_to_next(mgr, k): v
                              for k, v in trace[idx + first + 1].items()})
                assert simpl(subst(p, trace[idx + first])).is_true()
        for idx, s in enumerate(_hints_states):
            for p in s:
                assert simpl(subst(p, trace[idx + first])).is_true()
        for idx, t in enumerate(_hints_trans):
            for p in t:
                p = subst(p, {symb_to_next(mgr, k): v
                              for k, v in trace[idx + first + 1].items()})
                assert simpl(subst(p, trace[idx + first])).is_true()
    # last state implies first state : safe to copy predicates.
    _abst_states[-1] = _abst_states[0] | _abst_states[-1]
    _hints_states[-1] = _hints_states[0] | _hints_states[-1]

    # canonize transition relations
    # increases chance of detecting constant symbols syntactically.
    _abst_trans = [frozenset(cn(t) for t in trans) for trans in _abst_trans]
    _hints_trans = [frozenset(cn(t) for t in trans) for trans in _hints_trans]

    constant_symbs = _extract_constant_symbs(
        env, _symbs, trace, first,
        [s0 | s1 for s0, s1 in zip(_abst_states, _hints_states)],
        [t0 | t1 for t0, t1 in zip(_abst_trans, _hints_trans)],
        cn, totime)

    _hints_symbs = frozenset(chain.from_iterable(
        h.owned_symbs for h in _hints)) - constant_symbs
    _symbs = _symbs - constant_symbs

    # replace all constant symbs with their assignment.
    _conc_assigns = [{s: trace[idx][s]
                      for s in constant_symbs}
                     for idx in range(first, len(trace))]
    _abst_states, _abst_trans = _apply_assigns(env, _symbs, _conc_assigns,
                                               _abst_states, _abst_trans, cn)
    _hints_states, _hints_trans = _apply_assigns(env, _symbs, _conc_assigns,
                                                 _hints_states, _hints_trans,
                                                 cn)
    del _conc_assigns
    assert len(_hints_symbs & constant_symbs) == 0
    assert len(_symbs & constant_symbs) == 0
    assert all(len(env.fvo.get_free_variables(p) & constant_symbs) == 0
               for s in _abst_states for p in s)
    assert all(len(env.fvo.get_free_variables(p) & constant_symbs) == 0
               for t in _abst_trans for p in t)
    assert all(len(env.fvo.get_free_variables(p) & constant_symbs) == 0
               for s in _hints_states for p in s)
    assert all(len(env.fvo.get_free_variables(p) & constant_symbs) == 0
               for t in _hints_trans for p in t)

    lasso_symbs = frozenset(s for s in _symbs
                            if trace[first][s] == trace[-1][s])
    assert len(lasso_symbs & constant_symbs) == 0

    depends = _extract_dependencies(mgr,
                                    [abst_s | hint_s
                                     for abst_s, hint_s in zip(_abst_states,
                                                               _hints_states)])
    # remove all symbols that depend on non-lasso symbs
    restr_lasso_symbs = lasso_symbs
    _fixpoint = False
    while not _fixpoint:
        new = frozenset(s for s in restr_lasso_symbs
                        if depends[symb_to_next(mgr, s)] <= restr_lasso_symbs)
        _fixpoint = new == restr_lasso_symbs
        if not _fixpoint:
            restr_lasso_symbs = new
    del depends
    del _fixpoint

    assert len(restr_lasso_symbs & constant_symbs) == 0
    # First try to greedly fix the assignments of all current lasso vars
    # then remove those upon which some non-lasso symbs depend.
    lasso_symbs_lst = [lasso_symbs]
    if lasso_symbs != restr_lasso_symbs:
        lasso_symbs_lst.append(restr_lasso_symbs)

    if len(lasso_symbs) > 0 and len(restr_lasso_symbs) > 0:
        assert all(constant_symbs != symbs_lst
                   for symbs_lst in lasso_symbs_lst)
        lasso_symbs_lst.append(frozenset([]))

    del lasso_symbs
    del restr_lasso_symbs
    assert sorted(lasso_symbs_lst, key=len, reverse=True) == lasso_symbs_lst
    if __debug__:
        # each set should be contain all the following ones.
        for i, _ in enumerate(lasso_symbs_lst):
            for j in range(i+1, len(lasso_symbs_lst)):
                assert lasso_symbs_lst[i] >= lasso_symbs_lst[j]
    # save loop components for each set of lasso symbols.
    symbs_lst = []
    conc_assigns_lst = []
    abst_states_lst = []
    abst_trans_lst = []
    hints_symbs_lst = []
    hints_states_lst = []
    hints_trans_lst = []
    rank_rel = None
    # first try synth ranking functions from most general loop to most specific.
    for lasso_symbs in reversed(lasso_symbs_lst):
        symbs = _symbs - lasso_symbs
        conc_assigns = [{s: trace[idx][s]
                         for s in chain(lasso_symbs, constant_symbs)}
                        for idx in range(first, len(trace))]
        abst_states, abst_trans = _apply_assigns(env, symbs, conc_assigns,
                                                 _abst_states, _abst_trans, cn)
        hints_symbs = _hints_symbs - lasso_symbs
        hints_states, hints_trans = _apply_assigns(env, symbs, conc_assigns,
                                                   _hints_states,
                                                   _hints_trans, cn)
        assert all(not c.is_false() for s in abst_states for c in s)
        assert all(not c.is_false() for s in abst_trans for c in s)
        assert all(not c.is_false() for s in hints_states for c in s)
        assert all(not c.is_false() for s in hints_trans for c in s)
        assert all(len(env.ao.get_atoms(p)) == 1 for state in abst_states
                   for p in state), abst_states
        assert all(len(env.ao.get_atoms(t)) == 1 for trans in abst_trans
                   for t in trans), abst_trans
        assert all(len(env.ao.get_atoms(p)) == 1 for state in hints_states
                   for p in state), hints_states
        assert all(len(env.ao.get_atoms(t)) == 1 for trans in hints_trans
                   for t in trans), hints_trans
        assert all(cn(p) == p for s in abst_states for p in s)
        assert all(cn(p) == p for t in abst_trans for p in t)
        assert all(cn(p) == p for s in hints_states for p in s)
        assert all(cn(p) == p for t in hints_trans for p in t)

        if __debug__:
            simpl = env.simplifier.simplify
            subst = env.substituter.substitute
            for idx, s in enumerate(abst_states):
                for p in s:
                    assert simpl(subst(p, trace[idx + first])).is_true()
            for idx, t in enumerate(abst_trans):
                for p in t:
                    p = subst(p, {symb_to_next(mgr, k): v
                                  for k, v in trace[idx + first + 1].items()})
                    assert simpl(subst(p, trace[idx + first])).is_true()
            for idx, s in enumerate(hints_states):
                for p in s:
                    assert simpl(subst(p, trace[idx + first])).is_true()
            for idx, t in enumerate(hints_trans):
                for p in t:
                    p = subst(p, {symb_to_next(mgr, k): v
                                  for k, v in trace[idx + first + 1].items()})
                    assert simpl(subst(p, trace[idx + first])).is_true()

        rank_rel = None
        if get_use_rank_fun() and (get_use_ef_rf() or get_use_motzkin_rf()):
            log("\n\tTry synth ranking function for abstract loop, using hints: "
                f"{', '.join(str(h) for h in _hints) if _hints else None}",
                get_log_lvl())
            log("\n".join((f"\t\tState {idx + first}\n"
                           f"\t\t  State assigns: {', '.join(f'{serialize(k)} : {serialize(v)}' for k, v in assign.items())}\n"
                           f"\t\t  State: {', '.join(serialize(s) for s in state)}\n"
                           f"\t\t  Hint state: {', '.join(serialize(s) for s in region)}\n"
                           f"\t\t  Trans: {', '.join(serialize(t) for t in trans)}\n"
                           f"\t\t  Hint trans: {', '.join(serialize(t) for t in hint_trans)}")
                          for idx, (assign, state, trans, region, hint_trans) in
                          enumerate(zip(conc_assigns, abst_states, abst_trans,
                                        hints_states, hints_trans))),
                get_log_lvl())
            log(f"\t\tState {len(conc_assigns) + first - 1}\n"
                f"\t\t  State assigns: {', '.join(f'{serialize(k)} : {serialize(v)}' for k, v in conc_assigns[-1].items())}\n"
                f"\t\t  State: {', '.join(serialize(s) for s in abst_states[-1])}\n"
                f"\t\t  Hint state: {', '.join(serialize(s) for s in hints_states[-1])}",
                get_log_lvl())
            all_states = [s0 | s1 for s0, s1 in zip(abst_states, hints_states)]
            all_trans = [t0 | t1 for t0, t1 in zip(abst_trans, hints_trans)]
            ranker = Ranker(env, td, cn)
            for rank_t in ranker.rank_templates(symbs):
                log(f"\n\tUsing ranking template: {rank_t}", get_log_lvl())
                rank_rel = instantiate_rf_template(ranker, rank_t, all_states,
                                                   all_trans)
                if rank_rel:
                    rank_rel = rank_t.instantiate(rank_rel)
                    log(f"\tFound ranking relation: {rank_rel}", get_log_lvl())
                    break  # stop rf template iteration at first success.
        if rank_rel:  # stop candidate loop iteration at first success.
            break
        # we failed to synth a ranking function for this configuration.
        symbs_lst.append(symbs)
        conc_assigns_lst.append(conc_assigns)
        abst_states_lst.append(abst_states)
        abst_trans_lst.append(abst_trans)
        hints_symbs_lst.append(hints_symbs)
        hints_states_lst.append(hints_states)
        hints_trans_lst.append(hints_trans)

    assert len(symbs_lst) == len(conc_assigns_lst)
    assert len(symbs_lst) == len(abst_states_lst)
    assert len(symbs_lst) == len(abst_trans_lst)
    assert len(symbs_lst) == len(hints_symbs_lst)
    assert len(symbs_lst) == len(hints_states_lst)
    assert len(symbs_lst) == len(hints_trans_lst)
    assert len(symbs_lst) == 0 or \
        len(symbs_lst) == len(lasso_symbs_lst[-len(symbs_lst):])
    # try synth FunnelLoop for remaining loop candidates.
    for (lasso_symbs, symbs, conc_assigns, abst_states, abst_trans,
         hints_symbs, hints_states, hints_trans) in zip(
             lasso_symbs_lst[-len(symbs_lst):],
             reversed(symbs_lst), reversed(conc_assigns_lst),
             reversed(abst_states_lst), reversed(abst_trans_lst),
             reversed(hints_symbs_lst), reversed(hints_states_lst),
             reversed(hints_trans_lst)):
        # extract regions, equalities and transitions from hints.
        hints_states, hints_eqs, hints_trans = \
            _get_loop_components(env, symbs, hints_states, hints_trans,
                                 td, cn)
        assert last == first + len(hints_trans)
        assert len(hints_eqs) == len(hints_trans)
        assert len(hints_states) == len(hints_trans) + 1
        # extract regions, equalities and transitions from abstraction.
        abst_states, abst_eqs, abst_trans = \
            _get_loop_components(env, symbs, abst_states, abst_trans,
                                 td, cn, known_eqs=hints_eqs)
        assert last == first + len(abst_trans)
        assert len(abst_eqs) == len(abst_trans)
        assert len(abst_states) == len(abst_trans) + 1
        assert len(abst_states) == len(hints_states)

        log("\n\n\tTry synth FunnelLoop for abstract loop, using hints: "
            f"{', '.join(str(h) for h in _hints) if _hints else None}",
            get_log_lvl())
        log("\n".join((f"\t\tState {idx + first}\n"
                       f"\t\t  State assigns: {', '.join(f'{serialize(k)} : {serialize(v)}' for k, v in assign.items())}\n"
                       f"\t\t  State: {', '.join(serialize(s) for s in state)}\n"
                       f"\t\t  Hint state: {', '.join(serialize(s) for s in region)}\n"
                       f"\t\t  Trans assigns: {', '.join(f'{serialize(k)} = {serialize(v)}' for k, v in t_eqs.items())}\n"
                       f"\t\t  Trans: {', '.join(serialize(t) for t in trans)}\n"
                       f"\t\t  Hint assigns: {', '.join(f'{serialize(k)} = {serialize(v)}' for k, v in h_eq.items())}\n"
                       f"\t\t  Hint trans: {', '.join(serialize(t) for t in h_trans)}")
                      for idx, (assign, state, t_eqs, trans,
                                region, h_eq, h_trans) in
                      enumerate(zip(conc_assigns, abst_states,
                                    abst_eqs, abst_trans,
                                    hints_states, hints_eqs, hints_trans))),
            get_log_lvl())
        log(f"\t\tState {len(conc_assigns) + first - 1}\n"
            f"\t\t  State assigns: {', '.join(f'{serialize(k)} : {serialize(v)}' for k, v in conc_assigns[-1].items())}\n"
            f"\t\t  State: {', '.join(serialize(s) for s in abst_states[-1])}\n"
            f"\t\t  Hint State: {', '.join(serialize(s) for s in hints_states[-1])}",
            get_log_lvl())
        # try synth Funnel-loop.
        for nontermarg, num_ineqs in \
            FunnelLoop.factory(env, symbs, trace[first:], conc_assigns,
                               abst_states, abst_eqs, abst_trans,
                               hints_symbs,
                               hints_states, hints_eqs, hints_trans,
                               first, orig_trans):
            log(f"\n\tUsing template: {nontermarg.desc_template()}, "
                f"num ineqs: {num_ineqs}", get_log_lvl())
            log(nontermarg.describe(indent="\t"), get_log_lvl() + 1)
            model = instantiate_funnel_template(nontermarg)
            if model:
                return False, (trace, nontermarg, model)
    assert rank_rel in {None, False} or isinstance(rank_rel, RankFun)
    return True, rank_rel if rank_rel else None


def instantiate_rf_template(ranker: Ranker, rf: RankFun,
                            states: List[FrozenSet[FNode]],
                            trans: List[FrozenSet[FNode]]) \
        -> Union[Optional[bool], Dict[FNode, FNode]]:
    assert isinstance(ranker, Ranker)
    assert isinstance(ranker.env, PysmtEnv)
    assert isinstance(rf, RankFun)
    assert isinstance(states, list)
    assert all(isinstance(s, frozenset) for s in states)
    assert all(isinstance(p, FNode) for s in states for p in s)
    assert all(p in ranker.env.formula_manager.formulae.values()
               for s in states for p in s)
    assert isinstance(trans, list)
    assert all(isinstance(t, frozenset) for t in trans)
    assert all(isinstance(p, FNode) for t in trans for p in t)
    assert all(p in ranker.env.formula_manager.formulae.values()
               for t in trans for p in t)
    learn = None
    model = None
    if get_use_ef_rf():
        model, learn = ranker.ef_instantiate(rf, states, trans)
        assert all(c in ranker.env.formula_manager.formulae.values()
                   for c in learn)
        assert all(s in ranker.env.formula_manager.get_all_symbols()
                   for c in learn for s in ranker.env.fvo.walk(c))
        assert all(p in ranker.env.formula_manager.get_all_symbols()
                   for p in rf.params)
        assert all(ranker.env.fvo.walk(c) <= rf.params
                   for c in learn)

    if model is None and get_use_motzkin_rf():
        model = ranker.motzkin_instantiate(rf, states, trans,
                                           extra=learn if get_rf_learn_ef()
                                           else None)
    if model is not None and model is not False:
        assert isinstance(model, dict)
        assert all(isinstance(k, FNode) for k in model)
        assert all(isinstance(v, FNode) for v in model.values())
        assert all(k in ranker.env.formula_manager.formulae.values()
                   for k in model)
        assert all(v in ranker.env.formula_manager.formulae.values()
                   for v in model.values())
        if __debug__:
            err, msg = ranker._debug_check(model, rf, states, trans)
            assert err, msg
    return model


def instantiate_funnel_template(funnel_t: FunnelLoop) \
        -> Union[Optional[bool], Dict[FNode, FNode]]:
    assert isinstance(funnel_t, FunnelLoop)
    learn = None
    model = None
    if get_use_ef():
        model, learn = funnel_t.ef_instantiate()
        assert all(c in funnel_t.env.formula_manager.formulae.values()
                   for c in learn)
        assert all(s in funnel_t.env.formula_manager.get_all_symbols()
                   for c in learn
                   for s in funnel_t.env.fvo.walk(c))
        assert all(p in funnel_t.env.formula_manager.get_all_symbols()
                   for p in frozenset(funnel_t.parameters))
        assert all(funnel_t.env.fvo.walk(c) <= frozenset(funnel_t.parameters)
                   for c in learn)
    if model is None and get_use_motzkin():
        model = funnel_t.motzkin_instantiate(extra=learn if get_fun_learn_ef()
                                             else None)
    if model is not None and model is not False:
        assert isinstance(model, dict)
        assert all(isinstance(k, FNode) for k in model)
        assert all(isinstance(v, FNode) for v in model.values())
        assert all(k in funnel_t.env.formula_manager.formulae.values()
                   for k in model)
        assert all(v in funnel_t.env.formula_manager.formulae.values()
                   for v in model.values())
        if __debug__:
            valid, msg = funnel_t._debug_check(model)
            assert valid, msg
    return model


def _get_loop_components(env: PysmtEnv, symbs: FrozenSet[FNode],
                         abst_states: List[FrozenSet[FNode]],
                         abst_trans: List[FrozenSet[FNode]],
                         td: TimesDistributor, cn: Canonizer,
                         known_eqs: List[Dict[FNode, FNode]] = None) \
                    -> Tuple[List[FrozenSet[FNode]],
                             List[Dict[FNode, FNode]],
                             List[FrozenSet[FNode]]]:
    assert isinstance(env, PysmtEnv)
    assert isinstance(symbs, frozenset)
    assert all(isinstance(s, FNode) for s in symbs)
    assert all(s.is_symbol() for s in symbs)
    assert all(s in env.formula_manager.get_all_symbols() for s in symbs)
    assert isinstance(abst_states, list)
    assert all(isinstance(preds, frozenset) for preds in abst_states)
    assert all(isinstance(p, FNode) for preds in abst_states for p in preds)
    assert all(p in env.formula_manager.formulae.values()
               for preds in abst_states for p in preds)
    assert isinstance(abst_trans, list)
    assert all(isinstance(preds, frozenset) for preds in abst_trans)
    assert all(isinstance(p, FNode) for preds in abst_trans for p in preds)
    assert all(p in env.formula_manager.formulae.values()
               for preds in abst_trans for p in preds)
    assert known_eqs is None or isinstance(known_eqs, list)
    assert known_eqs is None or all(isinstance(eq, dict) for eq in known_eqs)
    assert known_eqs is None or all(isinstance(k, FNode)
                                    for eq in known_eqs for k in eq)
    assert known_eqs is None or all(isinstance(v, FNode)
                                    for eq in known_eqs for v in eq.values())
    assert known_eqs is None or all(k in env.formula_manager.formulae.values()
                                    for eq in known_eqs for k in eq)
    assert known_eqs is None or all(v in env.formula_manager.formulae.values()
                                    for eq in known_eqs for v in eq)
    assert len(abst_trans) == len(abst_states) - 1
    assert all(cn(p) == p for s in abst_states for p in s)
    assert all(cn(p) == p for t in abst_trans for p in t)
    assert known_eqs is None or len(known_eqs) == len(abst_trans)
    assert isinstance(td, TimesDistributor)
    assert isinstance(cn, Canonizer)

    simpl = env.simplifier.simplify
    subst = env.substituter.substitute
    mgr = env.formula_manager
    get_free_vars = env.fvo.walk

    res_states: List[Set[FNode]] = [set() for _ in abst_states]
    res_trans: List[Set[FNode]] = [set() for _ in abst_trans]
    # list of next symbol equalities
    res_eqs: List[Dict[FNode, FNode]] = [dict() for _ in abst_trans]
    for idx, abst_state in enumerate(abst_states):
        preds = list(abst_state)
        if idx == len(abst_states) - 1:
            # consider what we learned about first state.
            preds.extend(res_states[0])
        elif known_eqs is not None:
            eqs = known_eqs[idx]
        else:
            eqs = dict()
        abst_t_ineqs = []
        if idx < len(abst_trans):
            # first consider equalities
            preds.extend(t for t in abst_trans[idx] if t.is_equals())
            abst_t_ineqs = [t for t in abst_trans[idx] if not t.is_equals()]
        while preds:
            pred = preds.pop()
            assert len(env.ao.get_atoms(pred)) == 1
            assert not pred.is_true()
            assert not pred.is_not()
            pred = cn(pred)
            assert pred.is_lt() or pred.is_le() or pred.is_equals() or \
                pred.is_literal()
            if pred.is_equals():
                symb, expr, is_next_s = eq2assign(env, pred, td)
                if symb is not None:
                    if symb.is_true():
                        continue
                    if is_next_s:
                        assert isinstance(symb, FNode)
                        assert expr is not None
                        assert isinstance(expr, FNode)
                        assert symb.is_symbol()
                        if symb in res_eqs[idx] or \
                           symb in eqs:
                            # symb = a & symb = b -> a = b
                            eq = res_eqs[idx][symb] if symb in res_eqs[idx] \
                                else eqs[symb]
                            eq = simpl(mgr.Equals(eq, expr))
                            if not eq.is_true():
                                preds.append(eq)
                        else:
                            res_eqs[idx][symb] = expr
                        continue
                    if idx > 0:
                        x_pred = mgr.Equals(symb_to_next(mgr, symb),
                                            to_next(mgr, expr, symbs))
                        prev_eqs = known_eqs[idx - 1] if known_eqs else {}
                        x_pred = simpl(subst(x_pred, {**res_eqs[idx - 1],
                                                      **prev_eqs}))
                        symb, expr, is_next_s = eq2assign(env, x_pred, td)
                        if symb is not None:
                            if symb.is_true():
                                continue
                            if is_next_s:
                                assert isinstance(symb, FNode)
                                assert expr is not None
                                assert isinstance(expr, FNode)
                                assert symb.is_symbol()
                                assert symb not in res_eqs[idx - 1]
                                assert known_eqs is None or \
                                    symb not in known_eqs[idx - 1]
                                res_eqs[idx - 1][symb] = expr
                                continue
            assert all(symb_is_curr(s) for s in get_free_vars(pred))
            res_states[idx].add(pred)
        all_eqs = {**(res_eqs[idx]), **eqs} if idx < len(res_eqs) else {}
        # consider transition inequalities, apply all_eqs rewritings.
        while abst_t_ineqs:
            pred = abst_t_ineqs.pop()
            assert len(env.ao.get_atoms(pred)) == 1
            assert not pred.is_not()
            assert not pred.is_true()
            assert not pred.is_equals()
            assert cn(pred) == pred
            if all_eqs:
                pred = cn(simpl(subst(pred, all_eqs)))
            if pred.is_true():
                continue
            assert pred.is_lt() or pred.is_le() or pred.is_literal()

            if all(symb_is_curr(s) for s in get_free_vars(pred)):
                res_states[idx].add(pred)
            else:
                res_trans[idx].add(pred)

    assert len(res_eqs) == len(res_states) - 1
    assert len(res_eqs) == len(res_trans)
    assert all(symb_is_curr(s) for state in res_states
               for pred in state for s in get_free_vars(pred))
    assert all(symb_is_next(s) for eq in res_eqs for s in eq.keys())
    assert all((all(len(get_free_vars(t)) == 0 for t in trans) or
                any(symb_is_next(s) for t in trans
                    for s in get_free_vars(t)))
               for trans in res_trans)
    assert known_eqs is None or all(k not in res_eq
                                    for eqs, res_eq in zip(known_eqs, res_eqs)
                                    for k in eqs)
    return ([frozenset(s) for s in res_states], res_eqs,
            [frozenset(t) for t in res_trans])


def _extract_dependencies(mgr: FormulaManager,
                          exprs: Iterable) -> Dict[FNode, Set[FNode]]:
    """List of symbols that appear in expression where a symbol in symbs"""
    assert isinstance(exprs, Iterable)

    rv = defaultdict(set)
    get_free_vars = mgr.env.fvo.walk
    for ineq in chain.from_iterable(exprs):
        assert isinstance(ineq, FNode), type(ineq)
        assert ineq in mgr.formulae.values()
        assert len(ExprAtTime.collect_times(mgr, ineq)) == 0
        symbs = get_free_vars(ineq)
        if any(symb_is_next(s) for s in symbs) and \
           any(symb_is_curr(s) for s in symbs):
            curr_symbs = frozenset(s if symb_is_curr(s)
                                   else symb_to_curr(mgr, s)
                                   for s in symbs)
            for s in filter(symb_is_next, symbs):
                rv[s].update(curr_symbs)
    return rv


def _extract_constant_symbs(env: PysmtEnv,
                            symbs: FrozenSet[FNode],
                            trace: List[Dict[FNode, FNode]],
                            first: int,
                            states: List[FrozenSet[FNode]],
                            trans: List[FrozenSet[FNode]],
                            cn: Canonizer,
                            totime: ExprAtTime) -> FrozenSet[FNode]:
    assert isinstance(env, PysmtEnv)
    assert isinstance(symbs, frozenset)
    assert all(isinstance(s, FNode) for s in symbs)
    assert all(s in env.formula_manager.get_all_symbols() for s in symbs)
    assert isinstance(trace, list)
    assert all(isinstance(state, dict) for state in trace)
    assert all(isinstance(k, FNode) for state in trace for k in state)
    assert all(isinstance(v, FNode) for state in trace for v in state.values())
    assert all(k in env.formula_manager.get_all_symbols()
               for state in trace for k in state)
    assert all(v in env.formula_manager.formulae.values()
               for state in trace for v in state.values())
    assert all(env.stc.walk(s) == env.stc.walk(v)
               for state in trace for s, v in state.items())
    assert isinstance(states, list)
    assert isinstance(trans, list)
    assert len(states) + first == len(trace)
    assert len(states) == len(trans) + 1
    assert all(isinstance(s, frozenset) for s in states)
    assert all(isinstance(t, frozenset) for t in trans)
    assert all(cn(p) == p for t in trans for p in t)
    assert all(isinstance(p, FNode) for s in states for p in s)
    assert all(isinstance(p, FNode) for t in trans for p in t)
    assert all(p in env.formula_manager.formulae.values()
               for s in states for p in s)
    assert all(p in env.formula_manager.formulae.values()
               for t in trans for p in t)
    assert all(s in env.formula_manager.get_all_symbols()
               for state in states for p in state
               for s in env.fvo.walk(p))
    assert all(s in env.formula_manager.get_all_symbols()
               for tr in trans for p in tr
               for s in env.fvo.walk(p))
    assert all(isinstance(tr, frozenset) for tr in trans)
    assert all(isinstance(p, FNode) for tr in trans for p in tr)
    assert all(p in env.formula_manager.formulae.values()
               for tr in trans for p in tr)
    assert all(s in env.formula_manager.get_all_symbols()
               for tr in trans for p in tr for s in env.fvo.walk(p))
    assert all(cn(p) == p for tr in trans for p in tr)
    assert isinstance(totime, ExprAtTime)
    assert totime.env == env
    assert isinstance(cn, Canonizer)
    assert cn.env == env
    assert isinstance(first, int)
    assert first >= 0
    assert first < len(trace)

    mgr = env.formula_manager
    tc = env.stc.walk
    res = set()
    to_analyse_symbs = []
    for s in symbs:
        if tc(s).is_bool_type():
            # fixed assignment to all finite-state symbols.
            res.add(s)
        elif trace[first][s] == trace[-1][s]:
            # collect all symbols x such that x' = x holds in every transition.
            assert tc(s).is_real_type() or \
                tc(s).is_int_type()
            eq = cn(mgr.Equals(symb_to_next(mgr, s), s))
            if all(eq in tr for tr in trans):
                res.add(s)
            else:
                to_analyse_symbs.append(s)
    if len(to_analyse_symbs) > 0:
        assert all(tc(s).is_int_type() or tc(s).is_real_type()
                   for s in to_analyse_symbs)
        assertions = []
        # states
        assertions.extend(totime(pred, first + idx)
                          for idx, state in enumerate(states)
                          for pred in state)
        # abst_trans & hint_trans
        assertions.extend(totime(pred, first + idx)
                          for idx, tr in enumerate(trans)
                          for pred in tr)
        # add assignments we already discovered.
        assertions.extend(assign2fnode(env, totime(s, idx + first),
                                       step[s])
                          for idx, step in enumerate(trace[first:])
                          for s in res)
        assert all(isinstance(p, FNode) for p in assertions)
        with MultiSolver(env, get_extract_const_symbs_timeout(),
                         log_lvl=get_log_lvl() + 1) as solver:
            solver.add_assertions(assertions)
            solver.push()
            while to_analyse_symbs:
                s = to_analyse_symbs.pop()
                # unsat (states & trans & s_0 = v_0 & !(/\ s_i = v_i))
                solver.add_assertion(mgr.Equals(totime(s, first),
                                                trace[first][s]))
                solver.add_assertion(mgr.Not(mgr.And(
                    mgr.Equals(totime(s, idx + first + 1), x_step[s])
                    for idx, x_step in enumerate(trace[first+1:]))))
                try:
                    sat = solver.solve()
                except SolverReturnedUnknownResultError:
                    sat = None
                    solver.add_assertions(assertions)
                    solver.push()
                solver.pop()
                if sat is False:
                    res.add(s)
                    for idx, step in enumerate(trace[first:]):
                        eq = mgr.Equals(totime(s, idx + first), step[s])
                        solver.add_assertion(eq)
                solver.push()

    if __debug__:
        from solver import Solver
        # check validity of constant symbs.
        with Solver(env=env) as _solver:
            # abst_states & hint_states
            for idx, state in enumerate(states):
                c_time = idx + first
                for pred in state:
                    assert isinstance(pred, FNode)
                    _solver.add_assertion(totime(pred, c_time))
            for idx, tr in enumerate(trans):
                c_time = idx + first
                for pred in tr:
                    _solver.add_assertion(totime(pred, c_time))
            for s in res:
                _solver.add_assertion(assign2fnode(env, totime(s, first),
                                                   trace[first][s]))
            disj = []
            for idx, x_step in enumerate(trace[first+1:]):
                for s in res:
                    eq = assign2fnode(env, totime(s, idx + first + 1),
                                      x_step[s])
                    if tc(s).is_bool_type():
                        # assume finite state assignment.
                        _solver.add_assertion(eq)
                    else:
                        disj.append(eq)
            _solver.add_assertion(mgr.Not(mgr.And(disj)))
            assert _solver.solve() is False

    return frozenset(res)


def _apply_assigns(env: PysmtEnv,
                   symbs: FrozenSet[FNode],
                   assign_lst: List[Dict[FNode, FNode]],
                   state_lst: List[FrozenSet[FNode]],
                   trans_lst: List[FrozenSet[FNode]],
                   cn: Canonizer) \
                -> Tuple[List[FrozenSet[FNode]], List[FrozenSet[FNode]]]:
    assert isinstance(env, PysmtEnv)
    assert isinstance(symbs, frozenset)
    assert all(isinstance(s, FNode) for s in symbs)
    assert all(s in env.formula_manager.get_all_symbols() for s in symbs)
    assert isinstance(assign_lst, list)
    assert all(isinstance(assign, dict) for assign in assign_lst)
    assert all(isinstance(k, FNode) for assign in assign_lst for k in assign)
    assert all(isinstance(v, FNode)
               for assign in assign_lst for v in assign.values())
    assert all(k in env.formula_manager.get_all_symbols()
               for assign in assign_lst for k in assign)
    assert all(not symb_is_next(k)
               for assign in assign_lst for k in assign)
    assert all(env.fvo.walk(v) <= symbs
               for assign in assign_lst for v in assign.values())
    assert all(v in env.formula_manager.formulae.values()
               for assign in assign_lst for v in assign.values())
    assert isinstance(state_lst, list)
    assert all(isinstance(state, frozenset) for state in state_lst)
    assert all(isinstance(s, FNode) for state in state_lst for s in state)
    assert all(s in env.formula_manager.formulae.values()
               for state in state_lst for s in state)
    assert all(not s.is_false() for state in state_lst for s in state)
    assert all(not symb_is_next(s)
               for state in state_lst for p in state for s in env.fvo.walk(p))
    assert isinstance(trans_lst, list)
    assert all(isinstance(trans, frozenset) for trans in trans_lst)
    assert all(isinstance(t, FNode) for trans in trans_lst for t in trans)
    assert all(t in env.formula_manager.formulae.values()
               for trans in trans_lst for t in trans)
    assert all(not t.is_false() for trans in trans_lst for t in trans)
    assert all(any(symb_is_next(s) for s in env.fvo.walk(t))
               for trans in trans_lst for t in trans)
    assert len(assign_lst) == len(state_lst)
    assert len(state_lst) == len(trans_lst) + 1
    assert isinstance(cn, Canonizer)
    assert cn.env == env

    simpl = env.simplifier.simplify
    subst = env.substituter.substitute
    get_free_vars = env.fvo.walk
    mgr = env.formula_manager
    x_symbs = frozenset(symb_to_next(mgr, s) for s in symbs)

    res_state_lst = [set(filter(is_not_true, (cn(simpl(subst(s, assign)))
                                              for s in state)))
                     for assign, state in zip(assign_lst, state_lst)]
    res_trans_lst = []
    for assign, x_assign, trans, res_state in zip(assign_lst, assign_lst[1:],
                                                  trans_lst, res_state_lst):
        res_trans = set()
        for p in (cn(simpl(subst(subst(t, assign),
                                 {symb_to_next(mgr, k): v
                                  for k, v in x_assign.items()})))
                  for t in trans):
            if p.is_true():
                continue
            if len(get_free_vars(p) & x_symbs) > 0:
                res_trans.add(p)
            else:
                assert get_free_vars(p) <= symbs
                res_state.add(p)
        res_trans_lst.append(res_trans)

    assert all(not s.is_false()
               for state in res_state_lst for s in state)
    assert all(get_free_vars(s) <= symbs
               for state in res_state_lst for s in state)
    assert all(not s.is_true()
               for state in res_state_lst for s in state)
    assert all(len(get_free_vars(t) & x_symbs) > 0
               for trans in res_trans_lst for t in trans)
    assert all(cn(s) == s for state in res_state_lst for s in state)
    assert all(cn(t) == t for trans in res_trans_lst for t in trans)
    return ([frozenset(state) for state in res_state_lst],
            [frozenset(trans) for trans in res_trans_lst])
