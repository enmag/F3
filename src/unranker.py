from typing import Tuple, Union, Optional, List, Set, Dict
from itertools import chain
from collections.abc import Iterable
from collections import defaultdict

from pysmt.environment import Environment as PysmtEnv
from pysmt.formula import FormulaManager
from pysmt.fnode import FNode

from utils import log, default_key, symb_to_next, symb_to_curr, \
    symb_is_next, symb_is_curr, to_next
from ineq import eq_to_assign
from expr_at_time import ExprAtTime
from canonize import Canonizer
from rewritings import TimesDistributor
from abstract_loops import BMC
from funnel import NonterminationArg
from ranker import Ranker
from generalised_lasso import is_generalised_lasso

_USE_EF = True
_USE_EF_RF = True
_LEARN_EF = False
_USE_MOTZKIN = True
_USE_MOTZKIN_RF = True
# _SYNTH_RF = True
_USE_GENERALISED_LASSO = False
_NONTERM_FACTORY = "cartesian"
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


def set_learn_ef(val: bool) -> None:
    global _LEARN_EF
    assert isinstance(val, bool)
    _LEARN_EF = val


def get_learn_ef() -> bool:
    global _LEARN_EF
    return _LEARN_EF


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


def set_nonterm_factory(val: str) -> None:
    assert isinstance(val, str)
    global _NONTERM_FACTORY
    _NONTERM_FACTORY = val


def get_nonterm_factory_str() -> str:
    global _NONTERM_FACTORY
    return _NONTERM_FACTORY


def get_nonterm_factory():
    global _NONTERM_FACTORY
    if _NONTERM_FACTORY == "cartesian":
        return NonterminationArg.cartesian_factory
    if _NONTERM_FACTORY == "sat":
        return NonterminationArg.sat_factory
    return None


def set_use_generalised_lasso(val: bool) -> None:
    global _USE_GENERALISED_LASSO
    _USE_GENERALISED_LASSO = val


def get_use_generalised_lasso() -> bool:
    global _USE_GENERALISED_LASSO
    return _USE_GENERALISED_LASSO


def search_unrank_bmc(env: PysmtEnv, symbols: frozenset,
                      init: FNode, trans: FNode,
                      fair: FNode) -> Tuple[Optional[list],
                                            Optional[Union[NonterminationArg,
                                                           list, frozenset]],
                                            Optional[Union[dict, frozenset]]]:
    assert isinstance(env, PysmtEnv)
    assert isinstance(symbols, frozenset)
    assert isinstance(init, FNode)
    assert isinstance(trans, FNode)
    assert isinstance(fair, FNode)

    mgr = env.formula_manager
    simpl = env.simplifier.simplify
    init = simpl(init)
    trans = simpl(trans)
    fair = simpl(fair)
    totime = ExprAtTime(env=env)
    loop_gen = BMC(env, init, trans, fair, all_symbs=symbols)
    for i, (trace, lback_idx, abst_states, abst_trans) in \
            enumerate(loop_gen.gen_loops()):
        if trace is None:
            assert lback_idx is None
            assert abst_states is None
            assert abst_trans is None
            # We might have skipped some trace, not a problem.
            continue

        assert all(len(ExprAtTime.collect_times(mgr, k)) == 0
                   for state in trace for k in state)
        assert (abst_states is False and abst_trans is False) or \
            (abst_states is not False and abst_trans is not False)
        assert abst_states is False or isinstance(abst_states, list)
        assert abst_states is False or all(isinstance(s, frozenset)
                                           for s in abst_states)
        assert abst_states is False or \
            all(c in mgr.formulae.values() for s in abst_states for c in s)
        assert abst_states is False or \
            all(s in mgr.get_all_symbols()
                for state in abst_states for c in state
                for s in c.get_free_variables())
        assert abst_trans is False or isinstance(abst_trans, list)
        assert abst_trans is False or all(isinstance(t, frozenset)
                                          for t in abst_trans)
        assert abst_trans is False or \
            all(c in mgr.formulae.values() for t in abst_trans for c in t)
        assert abst_trans is False or \
            all(s in mgr.get_all_symbols()
                for t in abst_trans for c in t
                for s in c.get_free_variables())
        assert abst_states is False or len(abst_trans) == len(abst_states) - 1
        assert all(s in mgr.get_all_symbols()
                   for state in trace for s in state.keys())
        assert all(v in mgr.formulae.values()
                   for state in trace for v in state.values())
        assert all(s in mgr.get_all_symbols()
                   for state in trace for v in state.values()
                   for s in v.get_free_variables())

        log("\n\tBMC: found trace {}, len {}, lback {}".format(i, len(trace),
                                                               lback_idx),
            _LOG_LVL)
        for j, state in enumerate(trace):
            log("\t    State {} of trace {}".format(j, i), _LOG_LVL)
            for k in sorted(state.keys(), key=default_key):
                log("\t      {} : {}".format(k, state[k]), _LOG_LVL)
        log("\tEnd of trace {}\n".format(i), _LOG_LVL)

        if abst_states is False:
            assert abst_trans is False
            return trace[:lback_idx], trace[lback_idx:], None

        is_term, args = \
            synth_unrank(env, symbols, trace,
                         abst_states, abst_trans,
                         fair, lback_idx, totime, trans)
        if is_term and args is not None:
            assert isinstance(args, FNode)
            loop_gen.add_ranking_rel(args)
            # loop_gen.add_ranking_rels(args)

        if not is_term and args[1] is not None:
            assert isinstance(args, tuple)
            assert args[0] is not None
            assert args[1] is not None
            # either NontermArg or generalised lasso.
            return args

    return None, None, None


def synth_unrank(env: PysmtEnv, symbs: frozenset, trace: list,
                 _abst_states: list, _abst_trans: list,
                 fair: FNode, first: int, totime: ExprAtTime,
                 orig_trans):
    assert isinstance(env, PysmtEnv)
    assert isinstance(symbs, frozenset)
    assert isinstance(trace, list)
    assert all(isinstance(state, dict) for state in trace)
    assert isinstance(_abst_states, list)
    assert isinstance(_abst_trans, list)
    assert all(isinstance(it, frozenset) for it in _abst_states)
    assert all(isinstance(it, frozenset) for it in _abst_trans)
    assert all(c in env.formula_manager.formulae.values()
               for it in _abst_states
               for c in it)
    assert all(s in env.formula_manager.get_all_symbols()
               for it in _abst_states
               for c in it
               for s in c.get_free_variables())
    assert all(c in env.formula_manager.formulae.values()
               for it in _abst_trans
               for c in it)
    assert all(s in env.formula_manager.get_all_symbols()
               for it in _abst_trans
               for c in it
               for s in c.get_free_variables())
    assert isinstance(fair, FNode)
    assert fair in env.formula_manager.formulae.values()
    assert isinstance(totime, ExprAtTime)
    assert isinstance(first, int)
    assert first >= 0
    assert first < len(trace)
    assert len(_abst_states) + first == len(trace)
    assert len(_abst_states) == len(_abst_trans) + 1

    last = len(trace) - 1

    mgr = env.formula_manager
    subs = env.substituter.substitute
    simpl = env.simplifier.simplify
    cn = Canonizer(env=env)
    td = TimesDistributor(env=env)

    if get_use_generalised_lasso():
        res, div_pos, div_neg = \
            is_generalised_lasso(env, trace[first:], symbs,
                                 mgr.And(chain.from_iterable(chain(_abst_states,
                                                                   _abst_trans))),
                                 td)
        if res:
            return False, (trace[first:], div_pos, div_neg)

    # try to find ranking function for loop abstraction.
    all_finite_state_symbs = frozenset(s for s in symbs
                                       if s.symbol_type().is_bool_type())

    # collect all symbols x such that x' = x holds in every transition.
    all_constant_symbs = []
    for s in symbs - all_finite_state_symbs:
        x_s = symb_to_next(mgr, s)
        eq = cn(mgr.Equals(x_s, s))
        if all(eq in tr for tr in _abst_trans):
            all_constant_symbs.append(s)
    all_constant_symbs = frozenset(all_constant_symbs)

    # replace all boolean symbs with their assignment.
    _conc_assigns = [{s: trace[idx][s] for s in all_finite_state_symbs}
                     for idx in range(first, len(trace))]

    _abst_states = [frozenset(
        filter(lambda x: not x.is_true(),
               (simpl(subs(c, _conc_assigns[idx]))
                for c in s)))
                    for idx, s in enumerate(_abst_states)]
    assert all(not c.is_false() for s in _abst_states for c in s)

    _abst_trans = [frozenset(
        filter(lambda x: not x.is_true(),
               (simpl(subs(subs(c, _conc_assigns[idx]),
                           {symb_to_next(mgr, k): v
                            for k, v in _conc_assigns[idx + 1].items()}))
                for c in s)))
                   for idx, s in enumerate(_abst_trans)]
    assert all(not c.is_false() for s in _abst_trans for c in s)

    # try synth rank-fun for most general loop.
    if get_use_rank_fun():
        log("\n\tLoop abstraction", _LOG_LVL)
        log("\n".join(("\t\tState {}\n"
                       "\t\t  State assigns: {}\n"
                       "\t\t  State: {}\n"
                       "\t\t  Trans: {}").format(idx + first,
                                                 assign, state, trans)
                      for idx, (assign, state, trans) in
                      enumerate(zip(_conc_assigns, _abst_states,
                                    _abst_trans))),
            _LOG_LVL)
        log("\t\tState {}\n"
            "\t\t  State assigns: {}\n"
            "\t\t  State: {}".format(len(_conc_assigns) + first - 1,
                                     _conc_assigns[-1],
                                     _abst_states[-1]),
            _LOG_LVL)
        ranker = Ranker(env, td, cn)
        for rf in ranker.get_rf(symbs, _abst_states, _abst_trans, None):
            log("\n\tUsing ranking template: {}"
                .format(rf.desc_template()), _LOG_LVL)
            learn = None
            rf_model = None
            if get_use_ef_rf():
                rf_model, learn = rf.ef_instantiate(extra=learn)
                if __debug__ and learn:
                    assert all(c in mgr.formulae.values() for c in learn)
                    assert all(s in mgr.get_all_symbols()
                               for c in learn for s in c.get_free_variables())
                    assert all(p in mgr.get_all_symbols() for p in rf.params)
                    assert all(c.get_free_variables() <= rf.params
                               for c in learn)
            if rf_model is None and get_use_motzkin_rf():
                if not get_learn_ef():
                    learn = None
                rf_model = rf.motzkin_instantiate(extra=learn)

            if rf_model:
                if __debug__:
                    err, msg = rf._debug_check(rf_model)
                    assert err, msg.serialize()
                rf_rel = cn(simpl(rf.progress_pred(rf_model)))
                log("\tFound ranking relation: {}"
                    .format(rf_rel.serialize()), _LOG_LVL)
                return True, rf_rel

    if not get_use_ef() and not get_use_motzkin():
        return True, None

    all_lasso_symbs = frozenset(s for s in symbs
                                if trace[first][s] == trace[-1][s])
    assert all_lasso_symbs >= all_constant_symbs

    depends = extract_dependencies(mgr, _abst_trans)
    # remove all symbols that depend on non-lasso symbs
    restr_lasso_symbs = all_lasso_symbs
    _fixpoint = False
    while not _fixpoint:
        _fixpoint = True
        new = frozenset(s for s in restr_lasso_symbs
                        if depends[symb_to_next(mgr, s)] <= restr_lasso_symbs)
        if new != restr_lasso_symbs:
            _fixpoint = False
            restr_lasso_symbs = new

    # First try to greedly fix the assignments of all current lasso vars
    # then remove those upon which some non-lasso symbs depend.
    lasso_symbs_lst = [all_lasso_symbs]
    if all_lasso_symbs != restr_lasso_symbs:
        lasso_symbs_lst.append(restr_lasso_symbs | all_constant_symbs)

    if all(all_finite_state_symbs != symbs_lst
           for symbs_lst in lasso_symbs_lst):
        assert all(not s.symbol_type().is_real_type()
                   for s in all_finite_state_symbs)
        assert all(not s.symbol_type().is_int_type()
                   for s in all_finite_state_symbs)
        lasso_symbs_lst.append(all_finite_state_symbs | all_constant_symbs)

    # rank_rels = []
    rank_rel = None

    for lasso_symbs in lasso_symbs_lst:
        assert len(symbs - lasso_symbs) > 0
        assert all(not s.symbol_type().is_bool_type()
                   for s in symbs - lasso_symbs)
        if lasso_symbs == all_finite_state_symbs:
            conc_assigns = _conc_assigns
            abst_states = _abst_states
            abst_trans = _abst_trans
        else:
            conc_assigns = [{s: trace[idx][s] for s in lasso_symbs}
                            for idx in range(first, len(trace))]

            abst_states = [frozenset(
                filter(lambda x: not x.is_true(),
                       (simpl(subs(c, conc_assigns[idx]))
                        for c in s)))
                           for idx, s in enumerate(_abst_states)]

            abst_trans = [frozenset(
                filter(lambda x: not x.is_true(),
                       (simpl(subs(subs(c, conc_assigns[idx]),
                                   {symb_to_next(mgr, k): v
                                    for k, v in
                                    conc_assigns[idx + 1].items()}))
                        for c in s)))
                           for idx, s in enumerate(_abst_trans)]

        assert all(not c.is_false() for s in abst_states for c in s)
        assert all(not c.is_false() for s in abst_trans for c in s)
        assert all(len(p.get_atoms()) == 1 for state in abst_states
                   for p in state), abst_states
        assert all(len(t.get_atoms()) == 1 for trans in abst_trans
                   for t in trans), abst_trans

        # last state implies first state : safe to copy predicates.
        abst_states[-1] = abst_states[0] | abst_states[-1]

        abst_states, trans_eqs, abst_trans = \
            get_loop_components(env, symbs, abst_states, abst_trans, td, cn)

        assert last == first + len(abst_states) - 1

        log("\n\tLoop abstraction", _LOG_LVL)
        log("\n".join(("\t\tState {}\n"
                       "\t\t  State assigns: {}\n"
                       "\t\t  State: {}\n"
                       "\t\t  Trans assigns: {}\n"
                       "\t\t  Trans: {}").format(idx + first,
                                                 assign, state,
                                                 t_eqs, trans)
                      for idx, (assign, state, t_eqs, trans) in
                      enumerate(zip(conc_assigns, abst_states,
                                    trans_eqs, abst_trans))),
            _LOG_LVL)
        log("\t\tState {}\n"
            "\t\t  State assigns: {}\n"
            "\t\t  State: {}".format(len(conc_assigns) + first - 1,
                                     conc_assigns[-1],
                                     abst_states[-1]),
            _LOG_LVL)

        # try synth rank-fun.
        rf_model = None
        if get_use_rank_fun() and lasso_symbs != all_finite_state_symbs:
            ranker = Ranker(env, td, cn)
            for rf in ranker.get_rf(symbs, abst_states, abst_trans, trans_eqs):
                log("\n\tUsing ranking template: {}"
                    .format(rf.desc_template()), _LOG_LVL)
                learn = None
                if get_use_ef():
                    rf_model, learn = rf.ef_instantiate(extra=learn)
                    if __debug__ and learn:
                        assert all(c in mgr.formulae.values() for c in learn)
                        assert all(s in mgr.get_all_symbols()
                                   for c in learn
                                   for s in c.get_free_variables())
                        assert all(p in mgr.get_all_symbols()
                                   for p in rf.params)
                        assert all(c.get_free_variables() <= rf.params
                                   for c in learn)
                if rf_model is None and get_use_motzkin():
                    if not get_learn_ef():
                        learn = None
                    rf_model = rf.motzkin_instantiate(extra=learn)

                if rf_model:
                    if __debug__:
                        err, msg = rf._debug_check(rf_model)
                        assert err, msg
                    rf_rel = rf.progress_pred(rf_model)
                    log("\tFound ranking relation: {}"
                        .format(rf_rel.serialize()), _LOG_LVL)
                    rank_rel = cn(rf_rel)
                    # rank_rels.append(cn(rf_rel))
                    break

        if rf_model is None:
            nonterm_f = get_nonterm_factory()
            for nontermarg, num_ineqs in nonterm_f(env, symbs, trace[first:],
                                                   conc_assigns, abst_states,
                                                   trans_eqs, abst_trans,
                                                   first, orig_trans):
                log("\n\tUsing template: {}, num ineqs: {}"
                    .format(nontermarg.desc_template(), num_ineqs),
                    _LOG_LVL)
                log("{}".format(nontermarg.describe(indent="\t")),
                    _LOG_LVL + 1)
                learn = None
                arg = None
                if get_use_ef():
                    arg, learn = nontermarg.ef_instantiate()
                    if __debug__ and learn:
                        _mgr = nontermarg.env.formula_manager
                        assert all(c in _mgr.formulae.values() for c in learn)
                        assert all(s in _mgr.get_all_symbols()
                                   for c in learn
                                   for s in c.get_free_variables())
                        params = frozenset(nontermarg.parameters)
                        assert all(p in _mgr.get_all_symbols() for p in params)
                        assert all(c.get_free_variables() <= params
                                   for c in learn)
                if arg is None and get_use_motzkin():
                    learn = learn if get_learn_ef() else None
                    arg = nontermarg.motzkin_instantiate(extra=learn)
                if arg:
                    if __debug__:
                        valid, msg = nontermarg._debug_check(arg)
                        assert valid, msg
                    return False, (trace, nontermarg, arg)
                log("\n", _LOG_LVL)
    # return True, rank_rels
    return True, rank_rel


def get_loop_components(env: PysmtEnv, symbs: frozenset,
                        abst_states: list, abst_trans: list,
                        td: TimesDistributor,
                        cn: Canonizer) -> Tuple[List[Set[FNode]],
                                                List[Dict[FNode, FNode]],
                                                List[Set[FNode]]]:
    assert isinstance(env, PysmtEnv)
    assert isinstance(symbs, frozenset)
    assert all(s.is_symbol() for s in symbs)
    assert all(s in env.formula_manager.get_all_symbols() for s in symbs)
    assert isinstance(abst_states, list)
    assert all(isinstance(preds, frozenset) for preds in abst_states)
    assert isinstance(abst_trans, list)
    assert all(isinstance(preds, frozenset) for preds in abst_trans)
    assert len(abst_trans) == len(abst_states) - 1
    assert isinstance(td, TimesDistributor)
    assert isinstance(cn, Canonizer)

    simpl = env.simplifier.simplify
    subst = env.substituter.substitute
    mgr = env.formula_manager
    length = len(abst_states)
    res_states: List[Set[FNode]] = [set() for _ in range(length)]
    res_trans: List[Set[FNode]] = [set() for _ in range(length - 1)]
    # list of next symbol equalities
    res_eqs: List[Dict[FNode, FNode]] = [dict() for _ in abst_trans]
    for idx in range(len(abst_states)):
        preds = list(abst_states[idx])
        if idx == len(abst_states) - 1:
            # consider what we learned about first state.
            preds.extend(res_states[0])
        abst_t_ineqs = []
        if idx < len(abst_trans):
            # first consider equalities
            preds.extend(t for t in abst_trans[idx] if t.is_equals())
            abst_t_ineqs = [t for t in abst_trans[idx] if not t.is_equals()]
        while preds:
            pred = preds.pop()
            assert len(pred.get_atoms()) == 1
            assert not pred.is_true()
            assert not pred.is_not()
            pred = cn(pred)
            assert pred.is_lt() or pred.is_le() or pred.is_equals() or \
                pred.is_literal(), pred.serialize()
            if pred.is_equals():
                symb, expr, is_next_s = eq_to_assign(env, pred, td)
                if symb is not None:
                    if symb.is_true():
                        continue
                    if is_next_s:
                        assert isinstance(symb, FNode)
                        assert expr is not None
                        assert isinstance(expr, FNode)
                        assert symb.is_symbol()
                        if symb in res_eqs[idx]:
                            # symb = a & symb = b -> a = b
                            eq = res_eqs[idx][symb]
                            eq = simpl(mgr.Equals(eq, expr))
                            if not eq.is_true():
                                preds.append(eq)
                        else:
                            res_eqs[idx][symb] = expr
                        continue
                    elif idx > 0:
                        x_pred = mgr.Equals(symb_to_next(mgr, symb),
                                            to_next(mgr, expr, symbs))
                        x_pred = simpl(subst(x_pred, res_eqs[idx - 1]))
                        symb, expr, is_next_s = eq_to_assign(env, x_pred, td)
                        if symb is not None:
                            if symb.is_true():
                                continue
                            if is_next_s:
                                assert isinstance(symb, FNode)
                                assert expr is not None
                                assert isinstance(expr, FNode)
                                assert symb.is_symbol()
                                assert symb not in res_eqs[idx - 1]
                                res_eqs[idx - 1][symb] = expr
                                continue
            assert all(symb_is_curr(s) for s in pred.get_free_variables()), pred.serialize()
            res_states[idx].add(pred)
        # consider transition inequalities, apply res_eqs rewritings.
        while abst_t_ineqs:
            pred = abst_t_ineqs.pop()
            assert len(pred.get_atoms()) == 1
            assert not pred.is_not()
            assert not pred.is_true()
            assert not pred.is_equals()
            pred = cn(simpl(subst(pred, res_eqs[idx])))
            if pred.is_true():
                continue
            assert pred.is_lt() or pred.is_le() or pred.is_literal()

            if all(symb_is_curr(s) for s in pred.get_free_variables()):
                res_states[idx].add(pred)
            else:
                res_trans[idx].add(pred)

    assert len(res_eqs) == len(res_trans)
    assert all(symb_is_curr(s) for state in res_states
               for pred in state for s in pred.get_free_variables())
    assert all(symb_is_next(s) for eq in res_eqs for s in eq.keys())
    assert all((all(len(t.get_free_variables()) == 0 for t in trans) or
                any(symb_is_next(s) for t in trans
                    for s in t.get_free_variables()))
               for trans in res_trans)
    return res_states, res_eqs, res_trans


def extract_dependencies(mgr: FormulaManager,
                         exprs: Iterable) -> Dict[FNode, Set[FNode]]:
    """List of symbols that appear in expression where a symbol in symbs"""
    assert isinstance(exprs, Iterable)

    rv = defaultdict(set)
    for ineq in chain.from_iterable(exprs):
        assert isinstance(ineq, FNode), type(ineq)
        assert ineq in mgr.formulae.values()
        assert len(ExprAtTime.collect_times(mgr, ineq)) == 0
        symbs = ineq.get_free_variables()
        if any(symb_is_next(s) for s in symbs) and \
           any(symb_is_curr(s) for s in symbs):
            curr_symbs = frozenset(s if symb_is_curr(s)
                                   else symb_to_curr(mgr, s)
                                   for s in symbs)
            for s in filter(lambda x: symb_is_next(x), symbs):
                rv[s].update(curr_symbs)
    return rv
