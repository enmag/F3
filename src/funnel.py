from typing import Union, Optional, Tuple, List, Generator
from itertools import chain
from collections.abc import Iterable

from pysmt.environment import Environment as PysmtEnv
from pysmt.formula import FormulaContextualizer
from pysmt.fnode import FNode
import pysmt.typing as types
from pysmt.exceptions import SolverReturnedUnknownResultError

from expr_at_time import ExprAtTime
from rewritings import TimesDistributor
from canonize import Canonizer
from generalise_path import Generaliser
from solver import Solver, solve_with_timeout, get_solvers
from motzkin import motzkin_transpose
from efsolver import efsolve
from utils import symb_to_next, to_smt2, log, to_next, symb_is_curr, \
    assign_to_fnodes
from ineq import eq_to_assign


class NonterminationArg:
    """Encapsulate a non-termination argument: list of connected funnels"""

    _CONSTR_PROPAGATE = 1
    _MIN_INEQS = 0
    _MAX_INEQS = 2
    _TIMEOUT = 25
    _FILTER_TIMEOUT = 5
    _LOG_LVL = 1

    @staticmethod
    def set_timeout(val: int) -> None:
        assert isinstance(val, int)
        NonterminationArg._TIMEOUT = val

    @staticmethod
    def get_timeout() -> int:
        return NonterminationArg._TIMEOUT

    @staticmethod
    def set_filter_timeout(val: int) -> None:
        assert isinstance(val, int)
        NonterminationArg._FILTER_TIMEOUT = val

    @staticmethod
    def get_filter_timeout() -> int:
        return NonterminationArg._FILTER_TIMEOUT

    @staticmethod
    def set_constr_propagate(val: int) -> None:
        assert isinstance(val, int), val
        NonterminationArg._CONSTR_PROPAGATE = val

    @staticmethod
    def get_constr_propagate() -> int:
        return NonterminationArg._CONSTR_PROPAGATE

    @staticmethod
    def set_min_ineqs(val: int) -> None:
        assert isinstance(val, int), val
        assert val >= 0
        NonterminationArg._MIN_INEQS = val

    @staticmethod
    def get_min_ineqs() -> int:
        return NonterminationArg._MIN_INEQS

    @staticmethod
    def set_max_ineqs(val: int) -> None:
        assert isinstance(val, int), val
        assert val >= 0
        NonterminationArg._MAX_INEQS = val

    @staticmethod
    def get_max_ineqs() -> int:
        return NonterminationArg._MAX_INEQS

    @staticmethod
    def cartesian_factory(o_env: PysmtEnv, symbs: frozenset, trace: list,
                          conc_assigns: list, abst_states: list,
                          trans_eqs: list, abst_trans: list, first: int,
                          *args, **kwargs):
        """Generate different nontermination templates.

        Does not perform any heuristic reasoning,
        enumerates all templates compatible with the given trace:
        first try using only ConcFunnel,
        then a RFFunnel between every pair of candidate states.
        """
        assert isinstance(o_env, PysmtEnv)
        assert isinstance(symbs, (set, frozenset))
        assert all(s in o_env.formula_manager.get_all_symbols() for s in symbs)
        assert all(not ExprAtTime.is_timed_symb(o_env.formula_manager, s)
                   for s in symbs)
        assert isinstance(trace, Iterable)
        assert all(isinstance(s, dict) for s in trace)
        assert all(s in symbs for curr in trace for s in curr.keys())
        assert all(s in curr.keys() for curr in trace for s in symbs)
        assert all(not ExprAtTime.is_timed_symb(o_env.formula_manager, s)
                   for curr in trace for s in curr.keys())
        assert all(v.is_constant() for curr in trace for v in curr.values())
        assert isinstance(conc_assigns, list)
        assert all(isinstance(assign, dict) for assign in conc_assigns)
        assert all(k in symbs for assign in conc_assigns
                   for k in assign.keys())
        assert all(v.is_constant() for assign in conc_assigns
                   for v in assign.values())
        assert isinstance(abst_states, list)
        assert all(isinstance(state, (set, frozenset))
                   for state in abst_states)
        assert all(isinstance(e, FNode)
                   for state in abst_states for e in state)
        assert all(e.get_free_variables() <= symbs
                   for state in abst_states for e in state)
        assert isinstance(trans_eqs, list)
        assert all(isinstance(eq, dict) for eq in trans_eqs)
        assert all(k in frozenset(symb_to_next(o_env.formula_manager, s)
                                  for s in symbs)
                   for eq in trans_eqs for k in eq.keys())
        assert all(isinstance(v, FNode)
                   for eq in trans_eqs for v in eq.values())
        assert all(v in o_env.formula_manager.formulae.values()
                   for eq in trans_eqs for v in eq.values())
        assert isinstance(abst_trans, list)
        assert all(isinstance(t, (set, frozenset)) for t in abst_trans)
        assert all(isinstance(t, FNode) for trans in abst_trans for t in trans)
        assert all(t.get_free_variables() <=
                   symbs | frozenset(symb_to_next(o_env.formula_manager, s)
                                     for s in symbs)
                   for trans in abst_trans for t in trans)
        assert isinstance(first, int)
        assert first >= 0
        assert len(trace) == len(abst_states)
        assert len(conc_assigns) == len(abst_states)
        assert len(abst_trans) == len(abst_states) - 1
        assert len(trans_eqs) == len(abst_trans)

        idx2concfunnel = [True] * (len(abst_states) - 1)
        idx2key = [frozenset((_k, _v) for _k, _v in conc.items()
                             if not _k.symbol_name().startswith("_J"))
                   for conc in conc_assigns]
        _idx2rffunnel = [[c - 1 for c in range(idx+1, len(abst_states))
                          if idx2key[c] == idx2key[idx]]
                         for idx in range(len(abst_states))]
        del idx2key
        for num_ineqs in range(NonterminationArg.get_min_ineqs(),
                               NonterminationArg.get_max_ineqs() + 1):
            env = PysmtEnv()
            norm = FormulaContextualizer(env=env).walk
            totime = ExprAtTime(env=env, ignore_pref=Funnel.PREF)
            cn = Canonizer(env=env)
            td = TimesDistributor(env=env)

            symbs = frozenset(norm(s) for s in symbs)
            trace = [{norm(k): norm(v) for k, v in curr.items()}
                     for curr in trace]
            # init = {norm(k): norm(v) for k, v in trace[0].items()}
            conc_assigns = [{norm(k): norm(v) for k, v in assign.items()}
                            for assign in conc_assigns]
            abst_states = [frozenset(cn(norm(s)) for s in state)
                           for state in abst_states]
            trans_eqs = [{cn(norm(k)): cn(norm(v)) for k, v in eq.items()}
                         for eq in trans_eqs]
            abst_trans = [frozenset(cn(norm(t)) for t in abst_t)
                          for abst_t in abst_trans]

            idx2rffunnel = [[(i, trans_eqs[i], abst_trans[i])
                             for i in lst]
                            for lst in _idx2rffunnel]

            # single ConcFunnel
            nonterm_arg = NonterminationArg(env, td, cn, totime,
                                            init=trace[0])
                                            # init=trace[-1])
            nonterm_arg.append(ConcFunnel(env, first,
                                          first + len(abst_states) - 1,
                                          symbs,
                                          conc_assigns, abst_states, trans_eqs,
                                          abst_trans, num_ineqs, totime, cn))
            nonterm_arg.set_loop()
            yield nonterm_arg, num_ineqs

            yield from \
                NonterminationArg._generate_nonterm_args(env, first,
                                                         symbs, trace,
                                                         conc_assigns,
                                                         abst_states,
                                                         trans_eqs, abst_trans,
                                                         num_ineqs,
                                                         idx2concfunnel,
                                                         idx2rffunnel,
                                                         totime, td, cn)

    # @staticmethod
    # def sat_factory(o_env: PysmtEnv, symbs: frozenset, trace: list,
    #                 conc_assigns: list, abst_states: list,
    #                 trans_eqs: list, abst_trans: list, first: int,
    #                 orig_trans: FNode, *args, **kwargs):
    #     """Generate different nontermination templates.

    #     Try to prune templates that cannot be successful by performing
    #     additional SMT satifiability queries.
    #     In addition try to learn loop-back transitions for RFFunnels.
    #     """
    #     assert isinstance(o_env, PysmtEnv)
    #     assert isinstance(symbs, (set, frozenset))
    #     assert all(s in o_env.formula_manager.get_all_symbols() for s in symbs)
    #     assert all(not ExprAtTime.is_timed_symb(o_env.formula_manager, s)
    #                for s in symbs)
    #     assert isinstance(trace, Iterable)
    #     assert all(isinstance(s, dict) for s in trace)
    #     assert all(s in symbs for curr in trace for s in curr.keys())
    #     assert all(s in curr.keys() for curr in trace for s in symbs)
    #     assert all(not ExprAtTime.is_timed_symb(o_env.formula_manager, s)
    #                for curr in trace for s in curr.keys())
    #     assert all(v.is_constant() for curr in trace for v in curr.values())
    #     assert isinstance(conc_assigns, list)
    #     assert all(isinstance(assign, dict) for assign in conc_assigns)
    #     assert all(k in symbs for assign in conc_assigns
    #                for k in assign.keys())
    #     assert all(v.is_constant() for assign in conc_assigns
    #                for v in assign.values())
    #     assert isinstance(abst_states, list)
    #     assert all(isinstance(state, (set, frozenset))
    #                for state in abst_states)
    #     assert all(isinstance(e, FNode)
    #                for state in abst_states for e in state)
    #     assert all(e.get_free_variables() <= symbs
    #                for state in abst_states for e in state)
    #     assert isinstance(trans_eqs, list)
    #     assert all(isinstance(eq, dict) for eq in trans_eqs)
    #     assert all(k in frozenset(symb_to_next(o_env.formula_manager, s)
    #                               for s in symbs)
    #                for eq in trans_eqs for k in eq.keys())
    #     assert all(isinstance(v, FNode)
    #                for eq in trans_eqs for v in eq.values())
    #     assert all(v in o_env.formula_manager.formulae.values()
    #                for eq in trans_eqs for v in eq.values())
    #     assert isinstance(abst_trans, list)
    #     assert all(isinstance(t, (set, frozenset)) for t in abst_trans)
    #     assert all(isinstance(t, FNode) for trans in abst_trans for t in trans)
    #     assert all(t.get_free_variables() <=
    #                symbs | frozenset(symb_to_next(o_env.formula_manager, s)
    #                                  for s in symbs)
    #                for trans in abst_trans for t in trans)
    #     assert isinstance(first, int)
    #     assert first >= 0
    #     assert isinstance(orig_trans, FNode)
    #     assert len(trace) == len(abst_states)
    #     assert len(conc_assigns) == len(abst_states)
    #     assert len(abst_trans) == len(abst_states) - 1
    #     assert len(trans_eqs) == len(abst_trans)

    #     # idx2concfunnel = None
    #     idx2concfunnel = [True] * (len(abst_states) - 1)
    #     idx2rffunnel = None

    #     for num_ineqs in range(NonterminationArg.get_min_ineqs(),
    #                            NonterminationArg.get_max_ineqs() + 1):
    #         env = PysmtEnv()
    #         norm = FormulaContextualizer(env=env).walk
    #         totime = ExprAtTime(env=env, ignore_pref=Funnel.PREF)
    #         cn = Canonizer(env=env)
    #         td = TimesDistributor(env=env)
    #         symbs = frozenset(norm(s) for s in symbs)
    #         trace = [{norm(k): norm(v) for k, v in curr.items()}
    #                  for curr in trace]
    #         # init = {norm(k): norm(v) for k, v in init.items()}
    #         conc_assigns = [{norm(k): norm(v) for k, v in assign.items()}
    #                         for assign in conc_assigns]
    #         abst_states = [frozenset(cn(norm(s)) for s in state)
    #                        for state in abst_states]
    #         trans_eqs = [{cn(norm(k)): cn(norm(v)) for k, v in eq.items()}
    #                      for eq in trans_eqs]
    #         abst_trans = [frozenset(cn(norm(t)) for t in abst_t)
    #                       for abst_t in abst_trans]

    #         if idx2concfunnel is None:
    #             idx2concfunnel = \
    #                 NonterminationArg._concfunnel_filter(env, symbs, trace,
    #                                                      conc_assigns,
    #                                                      abst_states,
    #                                                      trans_eqs, abst_trans,
    #                                                      first, totime)
    #             assert isinstance(idx2concfunnel, list)
    #             assert len(idx2concfunnel) == len(abst_states) - 1
    #             assert all(isinstance(it, bool) for it in idx2concfunnel)

    #         if all(idx2concfunnel):
    #             # single ConcFunnel
    #             nonterm_arg = NonterminationArg(env, td, cn, totime,
    #                                             init=trace[0])
    #                                             # init=trace[-1])
    #             nonterm_arg.append(ConcFunnel(env, first,
    #                                           first + len(abst_states) - 1,
    #                                           symbs,
    #                                           conc_assigns, abst_states,
    #                                           trans_eqs, abst_trans,
    #                                           num_ineqs, totime, cn))
    #             nonterm_arg.set_loop()
    #             yield nonterm_arg, num_ineqs

    #         orig_trans = norm(orig_trans)
    #         generaliser = Generaliser(env, cn, totime)

    #         if idx2rffunnel is None:
    #             idx2rffunnel = \
    #                 NonterminationArg._rffunnel_candidates(env, symbs,
    #                                                        orig_trans,
    #                                                        trace,
    #                                                        conc_assigns,
    #                                                        abst_states,
    #                                                        trans_eqs,
    #                                                        abst_trans,
    #                                                        first,
    #                                                        totime, cn, td,
    #                                                        generaliser)
    #         else:
    #             idx2rffunnel = [[(idx,
    #                               {norm(k): norm(v) for k, v in eqs.items()},
    #                               frozenset(norm(p) for p in ineqs))
    #                              for idx, eqs, ineqs in it]
    #                             for it in idx2rffunnel]

    #         # print("\n\nConccandidates: {}".format(idx2concfunnel))
    #         # print("RFFcandidates: {}\n".format(idx2rffunnel))
    #         assert isinstance(idx2rffunnel, list)
    #         assert len(idx2rffunnel) == len(abst_states)
    #         assert all(isinstance(it, list) for it in idx2rffunnel)
    #         assert all(isinstance(el, tuple) for it in idx2rffunnel
    #                    for el in it)
    #         assert all(len(el) == 3 for it in idx2rffunnel for el in it)
    #         assert all(isinstance(el[0], int) for it in idx2rffunnel
    #                    for el in it)
    #         assert all(isinstance(el[1], dict) for it in idx2rffunnel
    #                    for el in it)
    #         assert all(isinstance(el[2], frozenset) for it in idx2rffunnel
    #                    for el in it)
    #         assert all(isinstance(el, FNode)
    #                    for lst in idx2rffunnel for it in lst
    #                    for el in it[1].keys())
    #         assert all(isinstance(el, FNode)
    #                    for lst in idx2rffunnel for it in lst
    #                    for el in it[1].values())
    #         assert all(isinstance(el, FNode)
    #                    for lst in idx2rffunnel for it in lst
    #                    for el in it[2])

    #         yield from \
    #             NonterminationArg._generate_nonterm_args(env, first,
    #                                                      symbs, trace,
    #                                                      conc_assigns,
    #                                                      abst_states,
    #                                                      trans_eqs, abst_trans,
    #                                                      num_ineqs,
    #                                                      idx2concfunnel,
    #                                                      idx2rffunnel,
    #                                                      totime, td, cn)

    @staticmethod
    def _generate_nonterm_args(env, first, symbs, trace,
                               _conc_assigns, _abst_states,
                               _trans_eqs, _abst_trans, num_ineqs,
                               idx2concfunnel, idx2rffunnel,
                               totime, td, cn):
        assert len(trace) == len(_abst_states)
        assert _conc_assigns[0] == _conc_assigns[-1]
        for n_rffunnels in range(1, len(_abst_states)):
            for lst in \
                NonterminationArg._generate_start_end_idx(0, n_rffunnels,
                                                          len(_abst_states),
                                                          idx2concfunnel,
                                                          idx2rffunnel):
                last_end = 0
                # bring first RFFunnel at the beginning.
                offset = lst[0][0] if lst else 0
                conc_assigns = _conc_assigns[offset: -1] + \
                    _conc_assigns[: offset + 1]
                # abst_states = _abst_states[offset: -1] + \
                #     _abst_states[: offset + 1]
                abst_states = _abst_states[offset:]
                abst_states[-1] = abst_states[-1] | _abst_states[0]
                abst_states += _abst_states[1: offset + 1]
                assert offset == 0 or abst_states[0] == abst_states[-1]
                assert len(abst_states) == len(conc_assigns)
                assert len(abst_states) == len(_abst_states)
                trans_eqs = _trans_eqs[offset:] + _trans_eqs[: offset]
                abst_trans = _abst_trans[offset:] + _abst_trans[: offset]

                nonterm_arg = NonterminationArg(env, td, cn, totime,
                                                offset=offset)
                nonterm_arg.set_init(trace[offset])
                # nonterm_arg.set_init(trace[-1 if offset == 0
                #                            else offset])
                for c_start, c_end, c_eqs, c_ineqs in lst:
                    c_start -= offset
                    c_end -= offset
                    assert c_start >= 0
                    assert c_end >= 0
                    assert c_end < len(abst_states)
                    assert c_end >= c_start
                    assert isinstance(c_ineqs, Iterable)
                    assert isinstance(c_eqs, dict), c_eqs
                    assert all(isinstance(ineq, FNode) for ineq in c_ineqs)
                    assert all(isinstance(k, FNode) for k in c_eqs.keys())
                    assert all(isinstance(v, FNode) for v in c_eqs.values())
                    if c_start > last_end:
                        assert all(idx2concfunnel[last_end + offset:
                                                  c_start + offset])
                        nonterm_arg.append(ConcFunnel(env,
                                                      first + last_end,
                                                      first + c_start,
                                                      symbs,
                                                      conc_assigns[last_end:
                                                                   c_start + 1],
                                                      abst_states[last_end:
                                                                  c_start + 1],
                                                      trans_eqs[last_end:
                                                                c_start],
                                                      abst_trans[last_end:
                                                                 c_start],
                                                      num_ineqs, totime, cn))
                    rf_t_eqs = trans_eqs[c_start: c_end] + [c_eqs]
                    rf_t_ineqs = abst_trans[c_start: c_end] + [c_ineqs]
                    nonterm_arg.append(RFFunnel(env,
                                                first + c_start,
                                                first + c_end,
                                                symbs,
                                                conc_assigns[c_start:
                                                             c_end + 1],
                                                abst_states[c_start:
                                                            c_end + 1],
                                                rf_t_eqs,
                                                rf_t_ineqs,
                                                num_ineqs, totime, cn))
                    last_end = c_end
                if last_end < len(abst_states) - 1:
                    # assert all(idx2concfunnel[last_end + offset + 1:])
                    nonterm_arg.append(ConcFunnel(env,
                                                  first + last_end,
                                                  first + len(abst_states) - 1,
                                                  symbs,
                                                  conc_assigns[last_end:],
                                                  abst_states[last_end:],
                                                  trans_eqs[last_end:],
                                                  abst_trans[last_end:],
                                                  num_ineqs, totime, cn))

                nonterm_arg.set_loop()
                yield nonterm_arg, num_ineqs

    @staticmethod
    def _concfunnel_filter(env: PysmtEnv, symbs: frozenset,
                           trace: list,
                           conc_assigns: list, abst_states: list,
                           trans_eqs: list, abst_trans: list,
                           first: int, totime: ExprAtTime):
        mgr = env.formula_manager

        idx2concfunnel = [None for _ in abst_states[:-1]]
        # first check if sequence of ConcFunnels is possible.
        with Solver(env=env) as solver:
            assertions = []
            # add last state assignments
            for eq in assign_to_fnodes(mgr,
                                       {totime(k, first): v
                                        for k, v in trace[-1].items()}):
                solver.add_assertion(eq)
                assertions.append(eq)
            for idx in range(len(abst_states) - 1):
                x_idx = idx + 1
                c_time = idx + first
                x_time = x_idx + first
                for t in abst_trans[idx]:
                    t = totime(t, c_time)
                    solver.add_assertion(t)
                    assertions.append(t)
                for k, v in trans_eqs[idx].items():
                    if __debug__:
                        from utils import symb_is_next
                        assert symb_is_next(k)
                    eq = mgr.Equals(totime(k, c_time), totime(v, c_time))
                    solver.add_assertion(eq)
                    assertions.append(eq)

                for p in abst_states[x_idx]:
                    solver.add_assertion(totime(p, x_time))
                for assign in assign_to_fnodes(mgr,
                                               {totime(k, x_time): v
                                                for k, v in conc_assigns[x_idx]
                                                .items()}):
                    solver.add_assertion(assign)
                is_sat = solver.solve()
                idx2concfunnel[idx] = is_sat

                if is_sat is False:
                    # TODO we could learn an interpolant.
                    # x_idx not reachable in 1 step.
                    solver.reset_assertions()
                    assertions = mgr.Not(mgr.And(assertions))
                    solver.add_assertion(assertions)
                    assertions = [assertions]
                    for eq in assign_to_fnodes(mgr,
                                               {totime(k, x_time): v
                                                for k, v in
                                                conc_assigns[x_idx].items()}):
                        solver.add_assertion(eq)
                        assertions.append(eq)
                    for p in abst_states[x_idx]:
                        p = totime(p, x_time)
                        solver.add_assertion(p)
                        assertions.append(p)
        return idx2concfunnel

    @staticmethod
    def _rffunnel_candidates(env: PysmtEnv, symbs: frozenset,
                             orig_trans: FNode,
                             trace: list,
                             conc_assigns: list, abst_states: list,
                             trans_eqs: list, abst_trans: list,
                             first: int, totime: ExprAtTime,
                             cn: Canonizer, td: TimesDistributor,
                             generalise: Generaliser):
        idx2rffunnel = [[] for _ in abst_states]
        simpl = env.simplifier.simplify
        subst = env.substituter.substitute
        mgr = env.formula_manager
        non_lasso_symbs = symbs - frozenset(conc_assigns[0].keys())

        with Solver(env=env) as solver:
            # iterate src state.
            for idx in range(len(abst_states) - 1):
                solver.reset_assertions()
                c_time = idx + first
                x_time = c_time + 1
                timed_symbs = [frozenset(totime(s, c_time) for s in symbs),
                               frozenset(totime(s, x_time) for s in symbs)]

                c_assumes = set()
                for p in abst_states[idx]:
                    p = totime(p, c_time)
                    assert p == cn(p)
                    solver.add_assertion(p)
                    c_assumes.add(p)
                # not the same state
                n_eqs = cn(mgr.Not(mgr.And(mgr.Equals(totime(s, x_time),
                                                      totime(s, c_time))
                                           for s in non_lasso_symbs)))
                solver.add_assertion(n_eqs)
                c_assumes.add(n_eqs)
                del n_eqs

                c_assumes = frozenset(c_assumes)

                # copy values of all symbols but justice monitors.
                i_orig_trans = simpl(subst(
                    orig_trans,
                    {k: v for k, v in conc_assigns[idx].items()
                     if not k.symbol_name().startswith("_J")}))

                # iterate dst state.
                for x_idx in range(0, idx + 1):
                    solver.push()
                    assumes = set(c_assumes)
                    c_assign = dict()
                    # copy assignments but justice monitors.
                    # allow reset of justice monitors.
                    for k, v in conc_assigns[x_idx].items():
                        x_k = symb_to_next(mgr, k)
                        if not k.symbol_name().startswith("_J"):
                            c_assign[x_k] = v
                        elif v.is_false():
                            c_assign[k] = v
                            c_assign[x_k] = v
                    c_orig_trans = simpl(subst(i_orig_trans, c_assign))
                    del c_assign
                    c_orig_trans = cn(totime(c_orig_trans, c_time))
                    solver.add_assertion(c_orig_trans)

                    for p in abst_states[x_idx]:
                        p = cn(totime(p, x_time))
                        solver.add_assertion(p)
                        assumes.add(p)

                    for a in c_orig_trans.get_atoms():
                        times = ExprAtTime.collect_times(mgr, a)
                        assert len(times) in [1, 2], a.serialize()
                        assert a == cn(a)
                        if len(times) == 1 and \
                           not (a.is_equals() and
                                max(times) == x_time and
                                len(a.get_free_variables()) == 1):
                            times = next(iter(times))
                            assert times in [c_time, x_time]
                            assumes.add(a)

                    assert all(cn(p) == p for p in assumes)
                    if solver.solve() is True:
                        cores = generalise(solver.assertions,
                                           solver.get_model(),
                                           timed_symbs,
                                           c_time, x_time,
                                           {p: solver.get_value(p)
                                            for p in assumes})
                        if __debug__:
                            # cores & assumes -> c_orig_trans.
                            _trans = subst(c_orig_trans,
                                           {p: solver.get_value(p)
                                            for p in assumes})
                            with Solver(env=env) as _solver:
                                for c in cores:
                                    _solver.add_assertion(c)
                                _solver.add_assertion(mgr.Not(_trans))
                                sat = _solver.solve()
                                assert sat is False
                            del _trans

                        core_eqs = {}
                        core_neqs = set()
                        for c in cores:
                            assert not c.is_true()
                            c = cn(totime(c, -c_time - 1))
                            assert c.is_lt() or c.is_le() or \
                                c.is_equals() or c.is_literal()
                            if c.is_equals():
                                symb, expr, is_next = eq_to_assign(env, c,
                                                                   td)
                                if symb is not None and symb not in core_eqs:
                                    assert symb.is_symbol()
                                    if __debug__:
                                        from utils import symb_is_next
                                        assert symb_is_next(symb)
                                    assert is_next
                                    if not symb.is_true():
                                        assert symb not in core_eqs
                                        assert expr is not None
                                        core_eqs[symb] = expr
                                    continue
                            core_neqs.add(c)
                        # print("\nfirst: {}, idx: {}, x_idx: {}"
                        #       .format(first, idx, x_idx))
                        # print("orig trans: {}"
                        #       .format(c_orig_trans.serialize()))
                        # print("core eqs:")
                        # for k, v in core_eqs.items():
                        #     print("\t{} : {}".format(k, v))
                        # print("cores neqs:")
                        # for p in core_neqs:
                        #     print("\t{}".format(p.serialize()))

                        idx2rffunnel[x_idx].append((idx, core_eqs,
                                                    frozenset(core_neqs)))
                    solver.pop()

        assert all(isinstance(it, list) for it in idx2rffunnel)
        assert all(isinstance(el, tuple) for it in idx2rffunnel for el in it)
        assert all(len(el) == 3 for it in idx2rffunnel for el in it)
        assert all(isinstance(el[0], int) for it in idx2rffunnel for el in it)
        assert all(isinstance(el[1], dict) for it in idx2rffunnel for el in it)
        assert all(isinstance(el[2], frozenset) for it in idx2rffunnel
                   for el in it)
        return idx2rffunnel

    @staticmethod
    def _generate_start_end_idx(start: int, n_rf_funnels: int, num_states: int,
                                idx2concf: list, idx2rff: list):
        assert isinstance(start, int)
        assert isinstance(n_rf_funnels, int)
        assert isinstance(num_states, int)
        assert start >= 0
        assert n_rf_funnels >= 0
        assert num_states > 1
        assert isinstance(idx2concf, list)
        assert len(idx2concf) == num_states - 1
        assert isinstance(idx2rff, list)
        assert len(idx2rff) == num_states
        assert all(isinstance(it, list) for it in idx2rff)
        assert all(isinstance(el, tuple) for it in idx2rff
                   for el in it)
        assert all(len(el) == 3 for it in idx2rff for el in it)
        assert all(isinstance(el[0], int) for it in idx2rff
                   for el in it)
        assert all(isinstance(el[1], dict) for it in idx2rff
                   for el in it)
        assert all(isinstance(el[2], frozenset) for it in idx2rff
                   for el in it)
        assert all(isinstance(el, FNode)
                   for lst in idx2rff for it in lst
                   for el in it[1].keys())
        assert all(isinstance(el, FNode)
                   for lst in idx2rff for it in lst
                   for el in it[1].values())
        assert all(isinstance(el, FNode)
                   for lst in idx2rff for it in lst
                   for el in it[2])

        def _gen_start_end_idx(start: int, n_rf_funnels: int,
                               num_states, idx2concf: list, idx2rff: list,
                               start_end_idx: list):
            last_end = start_end_idx[-1][1] if start_end_idx else 0
            for c_start in range(start, num_states):
                if not all(idx2concf[last_end: c_start]):
                    continue
                for c_end, eqs, neqs in idx2rff[c_start]:
                    assert isinstance(c_end, int)
                    assert isinstance(eqs, dict)
                    assert isinstance(neqs, frozenset)
                    start_end_idx.append((c_start, c_end, eqs, neqs))
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
                 init: Optional[dict] = None, offset: int = 0):
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
        self.parameters = set()
        self._funnels = []
        self._init = init if init else {}

    def set_init(self, init: dict) -> None:
        assert isinstance(init, dict)
        assert all(k in self.env.formula_manager.get_all_symbols()
                   for k in init.keys())
        assert all(v in self.env.formula_manager.formulae.values()
                   for v in init.values())
        assert all(v.is_constant() for v in init.values())
        self._init = init

    def append(self, funnel) -> None:
        """Ensure prev_f.last -> curr_f.first"""
        assert isinstance(funnel, Funnel)
        assert funnel.env == self.env
        self.parameters.update(funnel.parameters)
        if self._funnels:
            # link funnels together.
            last = self._funnels[-1]
            assert last.last == funnel.first
            assert last.states[-1] == funnel.states[0]
            assert last.assigns[-1] == funnel.assigns[0]
            funnel.strengthen_state(0, *last.last_ineqs)
            last.last_ineqs.extend(funnel.first_ineqs)
        self._funnels.append(funnel)
        assert len(self._funnels) < 2 or \
            self._funnels[-1].first == self._funnels[-2].last

    def set_loop(self) -> None:
        """Ensure last_f.last -> first_f.first"""
        assert len(self._funnels) >= 1
        self.parameters = frozenset(self.parameters)
        first_f = self._funnels[0]
        last_f = self._funnels[-1]
        assert last_f.last - first_f.first >= 1
        # assert all(s in last_f.states[-1] for s in first_f.states[0]), \
        #     (last_f.states[-1], first_f.states[0])
        assert last_f.assigns[-1] == first_f.assigns[0]

        # strengthen first state with last state
        first_f.strengthen_state(0, *last_f.states[-1])

        if NonterminationArg.get_constr_propagate():
            preds = frozenset(chain(first_f.first_ineqs,
                                    first_f.states[0]))
            assert all(self.cn(p) == p for p in preds), preds
            prev_f = first_f
            for f in reversed(self._funnels):
                if NonterminationArg.get_constr_propagate() == 1:
                    preds, keep = f.backward_propagate_partial(preds)
                else:
                    assert NonterminationArg.get_constr_propagate() == 2
                    preds, keep = f.backward_propagate(preds)
                f.strengthen_state(0, *preds)
                # print(type(f).__name__)
                # print("\tPREDS: {}".format([p.serialize() for p in preds]))
                # print("\tKEEP: {}".format([p.serialize() for p in keep]))
                if keep:
                    prev_f.strengthen_state(0, *keep)
                    f.last_ineqs.extend(keep)
                assert all(self.cn(p) == p for p in preds), preds
                assert all(self.cn(p) == p for p in keep), keep
                prev_f = f
            preds = preds - frozenset(first_f.first_ineqs)
            first_f.strengthen_state(0, *preds)
        last_f.last_ineqs.extend(first_f.first_ineqs)
        # last_f must imply first state.
        last_f.strengthen_state(-1, *first_f.states[0])

    def ef_instantiate(self, extra: Optional[Iterable] = None):
        res = None
        mgr = self.env.formula_manager
        simpl = self.env.simplifier.simplify
        subst = self.env.substituter.substitute
        generaliser = Generaliser(self.env, self.cn, self.totime)
        try:
            solver_it = iter(get_solvers())
            solver = next(solver_it)
            log("\tUsing solver {} for EF-constraints".format(solver),
                NonterminationArg._LOG_LVL)
            first_f = self._funnels[0]
            constrs = [simpl(subst(ineq, self._init))
                       for ineq in first_f.first_ineqs]
            constrs.extend(simpl(subst(abst_s, self._init))
                           for abst_s in first_f.states[0])
            constrs.extend(chain.from_iterable(f.constraints
                                               for f in self._funnels))
            if extra:
                constrs.extend(extra)

            constrs = mgr.And(constrs)
            symbs = constrs.get_free_variables() - self.parameters
            res, learn = efsolve(self.env, self.parameters, symbs,
                                 constrs, esolver_name=solver,
                                 fsolver_name=solver,
                                 generaliser=generaliser)
            constrs = mgr.And(constrs, mgr.And(learn))
            while res is None:
                solver = next(solver_it)
                log("\tUsing solver {} for EF-constraints".format(solver),
                    NonterminationArg._LOG_LVL)
                res, c_learn = efsolve(self.env, self.parameters, symbs,
                                       constrs,
                                       esolver_name=solver,
                                       fsolver_name=solver)
                constrs = mgr.And(constrs, mgr.And(c_learn))
                learn.extend(c_learn)
        except StopIteration:
            return None, learn
        return res, learn

    def motzkin_instantiate(self, extra: Optional[Iterable] = None):
        res = None
        solver_it = iter(get_solvers())
        extra = extra if extra else []
        try:
            solver = next(solver_it)
            log("\tUsing solver {} for motzkin-constraints".format(solver),
                NonterminationArg._LOG_LVL)

            with Solver(env=self.env, name=solver) as solver:
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
                    res = solve_with_timeout(NonterminationArg.get_timeout(),
                                             solver)
                except SolverReturnedUnknownResultError:
                    log("\t\tMotzkinUnranker timeout",
                        NonterminationArg._LOG_LVL)
                    log("\n{}\n".format(to_smt2(solver.assertions)),
                        NonterminationArg._LOG_LVL + 1)
                    res = None
                if res is True:
                    return solver.get_values(self.parameters)
                if res is False:
                    return None
                constrs = solver.assertions

            assert res is None, res
            assert constrs is not None

            while res is None:
                solver = next(solver_it)
                log("\tUsing solver {} for motzkin constraints".format(solver),
                    NonterminationArg._LOG_LVL)

                with Solver(env=self.env, name=solver) as solver:
                    for c in constrs:
                        assert c in self.env.formula_manager.formulae.values()
                        solver.add_assertion(c)
                    try:
                        res = solve_with_timeout(NonterminationArg.get_timeout(),
                                                 solver)
                    except SolverReturnedUnknownResultError:
                        log("\t\tMotzkinUnranker timeout",
                            NonterminationArg._LOG_LVL)
                        log("\n{}\n".format(to_smt2(solver.assertions)),
                            NonterminationArg._LOG_LVL + 1)
                        res = None

                    if res is True:
                        return solver.get_values(self.parameters)
                    if res is False:
                        return None
        except StopIteration:
            return None
        assert False, "unreachable code"

    def generate_motzkin_constr(self) -> Iterable:
        """Sequence of constraints generated via Motzkin transposition"""
        td = self.td
        cn = self.cn
        simpl = self.env.simplifier.simplify
        subst = self.env.substituter.substitute
        mgr = self.env.formula_manager

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
        # print("First: {}".format([f.serialize() for f in first]))
        assert all(constr.get_free_variables() <= self.parameters
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

                if all(s.get_free_variables() <= self.parameters
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
                                                     td, cn,
                                                     self.parameters)
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
        #                         print(to_smt2(mgr.Not(impl)))
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
        return "".join(f.describe(model, indent) for f in self._funnels) + \
            "\tstarting from: {}\n".format(self._init)

    def desc_template(self) -> str:
        """Return string description of current template"""
        res = "; ".join("{}(first: {}, last: {})"
                        .format(type(f).__name__, f.first, f.last)
                        for f in self._funnels)
        res += ", offset: {}".format(self.offset)
        return res

    def to_smv(self, trans: FNode, fair: FNode, model: dict, buf,
               orig_ltl: Optional[str] = None) -> None:
        from smv_printer import SMVPrinter
        assert len(self._funnels) > 0
        assert orig_ltl is None or isinstance(orig_ltl, str)
        symbs = self._funnels[0].all_symbs
        expr_print = SMVPrinter(buf, env=self.env)
        mgr = self.env.formula_manager
        state_var = "_f_state_"
        orig_trans_symb = "_orig_trans_"
        first = self._funnels[0].first
        last = self._funnels[-1].last
        buf.write("MODULE main\n")
        buf.write("  INVARSPEC NAME NOT_EMPTY := "
                  "!({0} = {1} & next({0}) = {2});\n"
                  .format(state_var, last, first))
        buf.write("  INVARSPEC NAME UNDERAPPROX := "
                  "({0} <= {1} & {1} < {2}) -> {3}"
                  .format(first, state_var, last, orig_trans_symb))
        buf.write(";\n")
        buf.write("  LTLSPEC NAME GF_FAIR := ")
        if orig_ltl is None:
            buf.write("G F ")
            expr_print.printer(fair)
        else:
            buf.write("! ")
            buf.write(orig_ltl)

        buf.write(";\n\n  DEFINE\n    {} := ".format(orig_trans_symb))
        expr_print.printer(trans)
        buf.write(";\n  VAR\n")
        buf.write("    {} : {}..{};\n".format(state_var, first, last))
        for s in symbs:
            buf.write("    ")
            expr_print.printer(s)
            buf.write(" : ")
            expr_print.smvtype(s.symbol_type())
            buf.write(";\n")
        buf.write("\n  -- initial state\n  INIT ")
        expr_print.printer(mgr.And(assign_to_fnodes(mgr, self._init)))

        buf.write(";\n\n  -- constant assignments\n")
        for f in self._funnels:
            for idx, assign in enumerate(f.assigns[:-1]):
                c_time = f.first + idx
                buf.write("  INVAR {} = {} -> (".format(state_var, c_time))
                expr_print.printer(mgr.And(assign_to_fnodes(mgr, assign)))
                buf.write(");\n")
        buf.write("  INVAR {} = {} -> (".format(state_var,
                                                self._funnels[-1].last))
        assign = self._funnels[-1].assigns[-1]
        expr_print.printer(mgr.And(assign_to_fnodes(mgr, assign)))
        buf.write(");\n\n  -- control flow graph for `{}`\n".format(state_var))

        buf.write("  ASSIGN\n    init({}) := {};\n".format(state_var, first))
        cfgs = [[] for _ in range(last - first)]
        for f in self._funnels:
            c_first = f.first - first
            for idx, c_cfg in enumerate(f.cfg(model)):
                cfgs[idx + c_first].append(c_cfg)
        buf.write("    next({}) :=\n      case\n".format(state_var))
        for idx, cfg in enumerate(cfgs):
            c_time = idx + first
            for x_time, cond in cfg:
                buf.write("        {} = {}".format(state_var, c_time))
                if cond:
                    buf.write(" & ")
                    expr_print.printer(cond)
                buf.write(" : {};\n".format(x_time))
        buf.write("        {} = {} : {};\n".format(state_var, last, first))
        buf.write("        TRUE : {};\n".format(state_var))
        buf.write("      esac;\n\n  -- link last with first state\n")

        buf.write("  TRANS ({0} = {1} & next({0}) = {2}) -> {3};\n".format(
            state_var, last, first, " & ".join("next({0}) = {0}".format(s)
                                               for s in symbs
                                               if not s.symbol_name()
                                               .startswith("_J"))
        ))

        for f in self._funnels:
            f.to_smv(model, state_var, buf, expr_print)

    def _debug_check(self, model) -> Tuple[bool, Optional[str]]:
        subst = self.env.substituter.substitute
        simpl = self.env.simplifier.simplify
        mgr = self.env.formula_manager
        first_f = self._funnels[0]
        with Solver(env=self.env) as solver:
            first_c = [simpl(subst(s, model)) for s in first_f.states[0]]
            first_c.extend([simpl(subst(s, model))
                            for s in first_f.first_ineqs])
            first_c = mgr.And(first_c)
            solver.add_assertion(first_c)
            if solver.solve() is not True:
                return False, "First UNSAT: {}".format(first_c.serialize())
            for init_assign in assign_to_fnodes(mgr, self._init):
                solver.add_assertion(init_assign)
            if solver.solve() is not True:
                return False, "Init not in first: {}".format(self._init)

        for f_num, f in enumerate(self._funnels):
            for c in f.constraints:
                if c.is_implies():
                    lhs = c.arg(0)
                    lhs = simpl(subst(lhs, model))
                    with Solver(env=self.env) as solver:
                        solver.add_assertion(lhs)
                curr = simpl(subst(c, model))
                with Solver(env=self.env) as solver:
                    # each constraint must be valid.
                    solver.add_assertion(mgr.Not(curr))
                    if solver.solve() is not False:
                        return False, "Funnel number {}, sat: {}"\
                            .format(f_num, c.serialize())
        return True, None


class Funnel:
    """Underapproximation leading from src to dst"""

    PREF = "_fun"

    def __init__(self, env: PysmtEnv, src_idx: int, dst_idx: int,
                 symbols: frozenset,
                 conc_assigns: list, states: list,
                 trans_eqs: list, trans: list,
                 num_ineqs: int,
                 totime: ExprAtTime, cn: Canonizer):
        assert isinstance(env, PysmtEnv)
        assert isinstance(src_idx, int)
        assert isinstance(dst_idx, int)
        assert isinstance(symbols, (set, frozenset))
        assert isinstance(conc_assigns, list)
        assert isinstance(states, list)
        assert isinstance(trans_eqs, list)
        assert isinstance(trans, list)
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
        assert all(len(s.get_atoms()) == 1 for state in states for s in state)
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
        assert all(len(t.get_atoms()) == 1
                   for s_trans in trans for t in s_trans)
        assert all(t in env.formula_manager.formulae.values()
                   for s_trans in trans for t in s_trans)
        assert all(cn(t) == t for s_trans in trans for t in s_trans)
        assert len(states) == dst_idx - src_idx + 1, (len(states), src_idx,
                                                      dst_idx)
        assert len(conc_assigns) == len(states)
        assert len(trans) == len(states) - 1 or len(trans) == len(states)
        assert len(trans_eqs) == len(trans)

        self.env = env
        self.mgr = env.formula_manager
        self._src_idx = src_idx
        self._dst_idx = dst_idx
        self.states = [set(state) for state in states]
        self.assigns = conc_assigns
        self.trans_eqs = trans_eqs
        self.last_ineqs: List[FNode] = []
        self.trans = trans
        self.totime = totime
        self.cn = cn
        self._c_symbs = frozenset(ExprAtTime.symb_untime(self.mgr, s)
                                  for s in conc_assigns[0])
        assert all(self.conc_symbs ==
                   frozenset(ExprAtTime.symb_untime(self.mgr, s)
                             for s in assign)
                   for assign in conc_assigns)

        symbs = symbols - self._c_symbs
        self._r_symbs = frozenset(s for s in symbs
                                  if s.symbol_type().is_real_type())
        self._i_symbs = frozenset(s for s in symbs
                                  if s.symbol_type().is_int_type())
        assert len(symbs) > 0
        assert (self._r_symbs | self._i_symbs) == symbs

        zero = self.mgr.Real(0) if self.real_symbs else self.mgr.Int(0)
        self._params = set()
        self._ineqs = []
        for _ in range(num_ineqs):
            expr, params = self._linear_comb(self.symbs_to_same_type)
            # expr, params = self._linear_comb(self.symbs_to_real)
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
    def first_ineqs(self) -> list:
        assert all(isinstance(ineq, FNode) for ineq in self._ineqs)
        return self._ineqs

    @property
    def parameters(self) -> frozenset:
        assert all(p in self.mgr.get_all_symbols() for p in self._params)
        return frozenset(self._params)

    @property
    def all_symbs(self) -> frozenset:
        return self.symbs | self.conc_symbs

    @property
    def conc_symbs(self) -> frozenset:
        return self._c_symbs

    @property
    def symbs_to_real(self) -> frozenset:
        return frozenset(self.mgr.ToReal(s)
                         for s in self.int_symbs) | self.real_symbs

    @property
    def symbs_to_same_type(self) -> frozenset:
        if self.real_symbs:
            return self.symbs_to_real
        return self.int_symbs

    @property
    def symbs(self) -> frozenset:
        return self.int_symbs | self.real_symbs

    @property
    def int_symbs(self) -> frozenset:
        return self._i_symbs

    @property
    def real_symbs(self) -> frozenset:
        return self._r_symbs

    @property
    def constraints(self):
        """Return iterable of Exist-Forall quantified constraints"""
        self.states = [frozenset(state) for state in self.states]
        for lhs, rhs in self._get_constr():
            assert isinstance(lhs, frozenset)
            assert isinstance(rhs, frozenset)
            assert all(isinstance(l, FNode) for l in lhs)
            assert all(isinstance(r, FNode) for r in rhs)
            yield self.simpl(self.mgr.Implies(self.mgr.And(lhs),
                                              self.mgr.And(rhs)))

    @property
    def implications(self):
        """Return pairs of implications [lhs] -> [rhs]

        lhs is purely conjunctive and rhs is purely disjunctive.
        """
        mgr = self.env.formula_manager
        self.states = [frozenset(state) for state in self.states]
        with Solver(env=self.env) as solver:
            for lhs, rhs in self._get_constr():
                assert isinstance(lhs, frozenset)
                assert isinstance(rhs, frozenset)
                assert all(isinstance(l, FNode) for l in lhs)
                assert all(isinstance(r, FNode) for r in rhs)
                assert all(l in mgr.formulae.values() for l in lhs)
                assert all(r in mgr.formulae.values() for r in rhs)
                solver.reset_assertions()
                assert len(solver.assertions) == 0
                # check if lhs -> rhs is VALID: unsat(lhs & !rhs)
                for l in lhs:
                    solver.add_assertion(l)
                # elements of lhs purely conjunctive
                # elements of rhs purely disjunctive
                for r in [atm for it in rhs
                          if not it.is_true() and it not in lhs
                          for atm in self.split_eq(it)
                          if atm not in lhs]:
                    assert isinstance(r, FNode)
                    solver.push()
                    solver.add_assertion(mgr.Not(r))
                    try:
                        res = solve_with_timeout(NonterminationArg.get_filter_timeout(),
                                                 solver)
                    except SolverReturnedUnknownResultError:
                        log("\t\tFunnel constraint filtering timeout",
                            NonterminationArg._LOG_LVL)
                        log("\n{}\n".format(to_smt2(solver.assertions)),
                            NonterminationArg._LOG_LVL + 1)
                        res = None
                    assert res in {True, False, None}
                    if res in {True, None}:
                        yield lhs, frozenset([r])
                    solver.pop()

    def strengthen_state(self, idx: int, *args) -> None:
        assert all(self.cn(s) == s for s in self.states[idx])
        self.states[idx].update(args)
        assert all(isinstance(a, FNode) for a in self.states[idx])
        assert all(self.cn(s) == s for s in self.states[idx])

    def simpl(self, formula: FNode) -> FNode:
        assert formula in self.mgr.formulae.values(), formula
        return self.env.simplifier.simplify(formula)

    def subst(self, formula: FNode, subs: dict) -> FNode:
        assert formula in self.mgr.formulae.values(), formula
        return self.env.substituter.substitute(formula, subs)

    def not_rel(self, rel: FNode) -> FNode:
        assert rel in self.mgr.formulae.values()
        if rel.is_true():
            return self.mgr.FALSE()
        if rel.is_false():
            return self.mgr.TRUE()

        assert rel.is_le() or rel.is_lt(), "{}".format(rel.serialize())
        lhs = rel.arg(0)
        rhs = rel.arg(1)
        rv = rel
        if rel.is_le():
            rv = self.mgr.GT(lhs, rhs)
        elif rel.is_lt():
            rv = self.mgr.GE(lhs, rhs)
        if __debug__:
            with Solver(env=self.env) as _solver:
                n_rv = self.mgr.Not(rv)
                equals = self.mgr.Iff(rel, n_rv)
                n_equals = self.mgr.Not(equals)
                _solver.add_assertion(n_equals)
                if _solver.solve():
                    assert False, "{}: {}".format(equals, _solver.get_model())
        return rv

    def split_eq(self, fm: FNode) -> list:
        assert isinstance(fm, FNode)
        if fm.is_equals():
            ge = self.mgr.GE(fm.arg(0), fm.arg(1))
            le = self.mgr.LE(fm.arg(0), fm.arg(1))
            return [ge, le]
        else:
            assert fm.is_constant() or fm.is_le() or fm.is_lt(), fm.serialize()
            return [fm]

    def cfg(self, model) -> list:
        res = []
        for idx in range(len(self.states[:-1])):
            res.append((self.first + idx + 1, None))
        return res

    # def to_smv(self, model, state_var, buf, expr_print):
    #     for idx, state in enumerate(self.states):
    #         if state:
    #             c_time = idx + self.first
    #             buf.write("INVAR ({} = {}) -> ".format(state_var, c_time))
    #             expr_print.printer(self.mgr.And(state))
    #             buf.write(";\n")

    def _new_symb(self, base: str, s_type) -> FNode:
        """Return fresh symbol of the given type"""
        assert s_type in {types.BOOL, types.INT, types.REAL}
        if base is None:
            base = "%d"
        base = "{}{}".format(Funnel.PREF, base)
        return self.mgr.new_fresh_symbol(s_type, base)

    def _linear_comb(self, symbs: Union[set, frozenset],
                     idx: Optional[int] = None) -> Tuple[FNode, list]:
        """Return FNode expr representing linear combination of symbs and
        list of parameters"""
        assert isinstance(symbs, (set, frozenset))
        assert idx is None or isinstance(idx, int), idx
        assert all(self.env.stc.get_type(s).is_int_type() for s in symbs) or \
            all(self.env.stc.get_type(s).is_real_type() for s in symbs)

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
            res.append(self.mgr.Times(coeff, s))
        res = self.mgr.Plus(res)
        assert all(p in self.mgr.get_all_symbols() for p in params)
        return res, params

    def __init_subclass__(cls, *args, **kwargs):
        super().__init_subclass__(*args, **kwargs)
        assert hasattr(cls, "_get_constr")
        assert hasattr(cls, "describe")
        assert hasattr(cls, "backward_propagate")


class ConcFunnel(Funnel):
    """Underapproximate each transition"""

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        assert len(self.trans) > 0
        assert len(self.trans) == self.last - self.first
        assert len(self.states) == len(self.trans) + 1

        n_trans = len(self.trans)
        self._u_trans = [{} for _ in range(n_trans)]
        for idx in range(n_trans):
            for s in self.symbs:
                x_s = symb_to_next(self.mgr, s)
                expr = self.trans_eqs[idx].get(x_s)
                if expr is None:
                    if s.symbol_type().is_real_type():
                        symbs = self.symbs_to_real
                    else:
                        assert s.symbol_type().is_int_type()
                        symbs = self.int_symbs
                    expr, params = self._linear_comb(symbs)
                    self._params.update(params)
                    expr = self.cn(expr)
                    assert all(p in self.mgr.get_all_symbols()
                               for p in self._params)
                assert x_s not in self._u_trans[idx]
                # TODO: we are storing expr both in trans_eqs and _u_trans
                self._u_trans[idx][x_s] = expr

    def _get_constr(self) -> Generator[Tuple[frozenset, frozenset],
                                       None, None]:
        # state[0] & ineqs & u_trans[:i] -> trans[i-1] & state[i]
        lhs = [self.totime(s, self.first) for s in self.states[0]]
        lhs.extend([self.totime(ineq, self.first)
                    for ineq in self.first_ineqs])
        for idx, _c_trans in enumerate(self._u_trans):
            x_idx = idx + 1
            c_time = idx + self.first
            x_time = c_time + 1
            lhs.extend(self.totime(self.mgr.Equals(u_symb, u_expr), c_time)
                       for u_symb, u_expr in _c_trans.items())
            # substitute current and next concrete assignments in trans.
            assignments = {**self.assigns[idx],
                           **{symb_to_next(self.mgr, k): v
                              for k, v in self.assigns[x_idx].items()}}
            rhs = [self.simpl(self.subst(t, assignments))
                   for t in self.trans[idx]]
            rhs = [self.totime(t, c_time)
                   for t in rhs]
            if x_idx == len(self.states) - 1:
                rhs.extend(self.totime(s, x_time) for s in self.last_ineqs)
            rhs.extend(self.totime(s, x_time) for s in self.states[x_idx])

            assert all(isinstance(l, FNode) for l in lhs)
            assert all(isinstance(r, FNode) for r in rhs)
            yield frozenset(lhs), frozenset(rhs)

    def backward_propagate(self, preds: Iterable) -> Tuple[frozenset,
                                                           frozenset]:
        """Push constraints on first state by applying transition equalities"""
        assert all(symb_is_curr(s) for p in preds
                   for s in p.get_free_variables())
        res = frozenset(preds) | frozenset(self.last_ineqs)
        assert all(self.cn(s) == s for s in res)
        for c_state, c_trans in reversed(list(zip(self.states[1:],
                                                  self._u_trans))):
            res = frozenset(self.cn(self.simpl(self.subst(to_next(self.mgr,
                                                                  pred,
                                                                  self.symbs),
                                                          c_trans)))
                            for pred in chain(res, c_state)
                            if not pred.is_true())
            c_state.clear()
            assert all(symb_is_curr(s) for p in res
                       for s in p.get_free_variables())
        res = frozenset(r for r in chain(res, self.states[0])
                        if not r.is_true())
        assert all(self.cn(s) == s for s in res)
        return res, frozenset()

    def backward_propagate_partial(self, preds: Iterable) -> Tuple[frozenset,
                                                                   frozenset]:
        res = frozenset(preds) | frozenset(self.last_ineqs)
        for c_state, c_trans in reversed(list(zip(self.states[1:],
                                                  self._u_trans))):
            keys = frozenset(k for k, v in c_trans.items()
                             if v.get_free_variables() <= self.symbs)
            c_preds = frozenset(res) | frozenset(c_state)
            c_state.clear()
            res = set()
            for p in c_preds:
                x_p = to_next(self.mgr, p, self.symbs)
                if x_p.get_free_variables() <= keys:
                    prop_p = self.simpl(self.subst(x_p, c_trans))
                    prop_p = self.cn(prop_p)
                    if not prop_p.is_true():
                        res.add(self.cn(prop_p))
                else:
                    c_state.add(p)
        assert all(symb_is_curr(s) for p in res
                   for s in p.get_free_variables())
        assert all(self.cn(s) == s for s in res)
        return frozenset(res), frozenset()

    def describe(self, param2val: dict, indent: str) -> str:
        assert isinstance(param2val, dict)
        assert isinstance(indent, str)
        assert all(p in param2val for p in self.parameters)
        ineqs = [self.simpl(self.subst(ineq, param2val))
                 for ineq in self.first_ineqs]
        u_trans = [{u_s: self.simpl(self.subst(u_e, param2val))
                    for u_s, u_e in trans.items()}
                   for trans in self._u_trans]
        res = ""
        for c_time in range(self.first, self.last):
            idx = c_time - self.first
            res += "{}State {}\n".format(indent, c_time)
            for s, val in self.assigns[idx].items():
                res += "{}\t{} = {}\n".format(indent,
                                              s.serialize(), val.serialize())
            for s in self.states[idx]:
                res += "{}\t{}\n"\
                    .format(indent,
                            self.simpl(self.subst(s, param2val)).serialize())
            if idx == 0:
                for ineq in ineqs:
                    res += "{}\t{}\n".format(indent, ineq.serialize())
            res += "{}Trans {} -- {}\n".format(indent, c_time, c_time + 1)
            for s, expr in u_trans[idx].items():
                res += "{}\t{} = {}\n".format(indent, s.serialize(),
                                              expr.serialize())
        return res

    def to_smv(self, model, state_var, buf, expr_print) -> None:
        buf.write("\n-- ConcFunnel\n")
        u_trans = [{u_s: self.simpl(self.subst(u_e, model))
                    for u_s, u_e in trans.items()}
                   for trans in self._u_trans]

        assert len(self.assigns) == len(u_trans) + 1
        for idx, trans in enumerate(u_trans):
            c_time = idx + self.first
            x_time = c_time + 1
            trans = self.mgr.And(self.mgr.Equals(k, v)
                                 for k, v in trans.items())
            buf.write("  -- transition from {} to {}\n".format(c_time,
                                                               x_time))
            buf.write("  TRANS ({0} = {1} & next({0}) = {2}) ->\n    (\n     "
                      .format(state_var, c_time, x_time))
            expr_print.printer(trans)
            buf.write("\n    );\n")

        buf.write("INVARSPEC NAME "
                  "CFUN{0}_STATE_{0} := ({1} = {0} & next({1}) = {2}) -> "
                  .format(self.first, state_var, self.first + 1))
        invar = list(self.first_ineqs) + list(self.states[0])
        expr_print.printer(self.simpl(self.subst(self.mgr.And(invar), model)))
        buf.write(";\n")

        for idx, s in enumerate(self.states[1:]):
            s_idx = idx + 1 + self.first
            buf.write("INVARSPEC NAME CFUN{2}_STATE_{0} := {1} = {0} -> "
                      .format(s_idx, state_var, self.first))
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
        self._rf_expr, params = \
            self._linear_comb(self.symbs_to_real)
            # self._linear_comb(self.symbs_to_same_type)
        self._rf_expr = self.cn(self._rf_expr)
        rf_type = self.env.stc.get_type(self._rf_expr)
        self._rf_zero = self.mgr.Real(0) if rf_type.is_real_type() \
            else self.mgr.Int(0)
        self._rf_pred = self.cn(self.mgr.GT(self._rf_expr, self._rf_zero))
        self._params.update(params)
        assert all(p in self.mgr.get_all_symbols() for p in self._params)
        self._delta = self._new_symb("_d%d", rf_type)
        self._params.add(self._delta)

        assert len(self.last_ineqs) == 0
        self.last_ineqs.append(self.cn(self.not_rel(self._rf_pred)))

        n_trans = len(self.trans)
        self._u_trans = [{} for _ in range(n_trans)]
        for idx in range(n_trans):
            for s in self.symbs:
                x_s = symb_to_next(self.mgr, s)
                # TODO: we are storing expr both in trans_eqs and _u_trans
                expr = self.trans_eqs[idx].get(x_s)
                if expr is None:
                    if s.symbol_type().is_real_type():
                        symbs = self.symbs_to_real
                    else:
                        assert s.symbol_type().is_int_type()
                        symbs = self.int_symbs
                    expr, params = self._linear_comb(symbs)
                    self._params.update(params)
                    expr = self.cn(expr)
                    assert all(p in self.mgr.get_all_symbols()
                               for p in self._params)
                assert x_s not in self._u_trans[idx]
                self._u_trans[idx][x_s] = expr

    def _get_constr(self) -> Generator[Tuple[frozenset, frozenset],
                                       None, None]:
        assert self.first + len(self._u_trans) == self.last + 1
        assert len(self._u_trans) == len(self.states)

        # delta >= 0
        yield frozenset([self.mgr.TRUE()]), \
            frozenset([self.mgr.GE(self._delta, self._rf_zero)])

        # ineqs & state[:i] & u_trans[:i] -> trans[i-1] & state[i]
        lhs = [self.totime(ineq, self.first) for ineq in self.first_ineqs]
        lhs.extend(self.totime(s, self.first) for s in self.states[0])
        for idx, _c_trans in enumerate(self._u_trans[:-1]):
            c_time = idx + self.first
            x_idx = idx + 1
            x_time = x_idx + self.first
            # lhs.extend(self.totime(s, c_time) for s in self.states[idx])
            lhs.extend(self.totime(self.mgr.Equals(u_symb, u_expr), c_time)
                       for u_symb, u_expr in _c_trans.items())
            # substitute current and next concrete assignments in trans.
            assignments = {**self.assigns[idx],
                           **{symb_to_next(self.mgr, k): v
                              for k, v in self.assigns[x_idx].items()}}
            rhs = [self.totime(self.simpl(self.subst(t, assignments)), c_time)
                   for t in self.trans[idx]]
            rhs.extend(self.totime(s, x_time) for s in self.states[x_idx])

            assert all(isinstance(l, FNode) for l in lhs)
            assert all(isinstance(r, FNode) for r in rhs)
            yield frozenset(lhs), frozenset(rhs)

        c_time = self.last
        # first_ineqs & states & u_trans & rf < 0 -> last_ineqs
        not_ranked = self.cn(self.totime(self.not_rel(self._rf_pred),
                                         c_time))
        lhs.append(not_ranked)
        assert self.last_ineqs[0] == self.cn(self.not_rel(self._rf_pred))
        rhs = frozenset(self.totime(l_ineq, c_time)
                        for l_ineq in self.last_ineqs[1:])
        yield frozenset(lhs), rhs

        # ineqs & states & u_trans & rf >= 0 & last_t -> trans & state[0]' & ineqs'
        lhs.pop()
        assert not_ranked not in lhs
        x_time = c_time + 1
        # rf >= 0
        _lhs = lhs + [self.totime(self._rf_pred, c_time)]
        # last_t
        _lhs.extend(self.totime(self.mgr.Equals(u_symb, u_expr), c_time)
                    for u_symb, u_expr in self._u_trans[-1].items())
        # trans
        last_t_assign = {**self.assigns[-1],
                         **{symb_to_next(self.mgr, k): v
                            for k, v in self.assigns[0].items()}}
        rhs = [self.totime(self.simpl(self.subst(t, last_t_assign)),
                           c_time)
               for t in self.trans[-1]]
        # ineqs'
        rhs.extend(self.totime(ineq, x_time) for ineq in self.first_ineqs)
        # state[0]'
        rhs.extend(self.totime(s, x_time) for s in self.states[0])
        yield frozenset(_lhs), frozenset(rhs)

        # rf >= 0 & last_t & state[0] & first_ineqs & u_trans -> decrease(rf)
        # assert self.first > 0
        start_t = self.last + 3  # cannot use self.first - 1 (first might be 0)
        end_t = self.first
        # rf >= 0
        lhs.append(self.totime(self._rf_pred, start_t, x_idx=end_t))
        # last_t
        lhs.extend(self.totime(self.mgr.Equals(u_symb, u_expr), start_t,
                               x_idx=end_t)
                   for u_symb, u_expr in self._u_trans[-1].items())

        dec_rf = self.mgr.Minus(self.totime(self._rf_expr, start_t,
                                            x_idx=end_t),
                                self._delta)
        dec_rf = self.mgr.LT(self.totime(self._rf_expr, self.last), dec_rf)
        assert isinstance(dec_rf, FNode)
        yield frozenset(lhs), frozenset([dec_rf])

    def backward_propagate(self, preds: Iterable) -> Tuple[frozenset,
                                                           frozenset]:
        """Push constraints on first state via transition relation"""
        assert all(symb_is_curr(s) for p in preds
                   for s in p.get_free_variables())
        res = set()
        keep = set()
        with Solver(env=self.env) as solver:
            for idx, c_trans in enumerate(self._u_trans):
                for s, expr in c_trans.items():
                    assert not symb_is_curr(s)
                    s = self.totime(s, idx)
                    expr = self.totime(expr, idx)
                    solver.add_assertion(self.mgr.Equals(s, expr))
            end = len(self._u_trans)
            # check which predicates are preserved by backward transition.
            for p in preds:
                p0 = self.totime(p, 0)
                pend = self.totime(p, end)
                solver.push()
                solver.add_assertion(pend)
                solver.add_assertion(self.mgr.Not(p0))
                sat = None
                try:
                    sat = solve_with_timeout(NonterminationArg.get_timeout(),
                                             solver)
                except SolverReturnedUnknownResultError:
                    sat = None
                solver.pop()
                if sat is False:
                    res.add(p)
                else:
                    keep.add(p)

        assert all(symb_is_curr(s) for p in res
                   for s in p.get_free_variables())
        assert all(self.cn(p) == p for p in res)
        assert all(self.cn(s) == s for s in keep)

        assert len(self.states) == len(self._u_trans)
        for c_state, c_trans in reversed(list(zip(self.states[1:],
                                                  self._u_trans[:-1]))):
            res = frozenset(self.cn(self.simpl(self.subst(to_next(self.mgr,
                                                                  pred,
                                                                  self.symbs),
                                                          c_trans)))
                            for pred in chain(res, c_state)
                            if not pred.is_true())
            c_state.clear()
            assert all(symb_is_curr(s) for p in res
                       for s in p.get_free_variables())
        res = frozenset(r for r in res if not r.is_true())
        assert all(self.cn(s) == s for s in res)
        # res = res | self.states[0]
        # self.states[0].clear()

        assert all(self.cn(s) == s for s in res)
        assert all(self.cn(s) == s for s in keep)
        return res, frozenset(keep)

    def backward_propagate_partial(self, preds: Iterable) -> Tuple[frozenset,
                                                                   frozenset]:
        """Push constraints on first state via transition relation"""
        assert all(symb_is_curr(s) for p in preds
                   for s in p.get_free_variables())
        res = set()
        keep = set()
        with Solver(env=self.env) as solver:
            for idx, c_trans in enumerate(self._u_trans):
                for s, expr in c_trans.items():
                    assert not symb_is_curr(s)
                    s = self.totime(s, idx)
                    expr = self.totime(expr, idx)
                    solver.add_assertion(self.mgr.Equals(s, expr))
            end = len(self._u_trans)
            # check which predicates are preserved by backward transition.
            for p in preds:
                p0 = self.totime(p, 0)
                pend = self.totime(p, end)
                solver.push()
                solver.add_assertion(pend)
                solver.add_assertion(self.mgr.Not(p0))
                sat = None
                try:
                    sat = solve_with_timeout(NonterminationArg.get_timeout(),
                                             solver)
                except SolverReturnedUnknownResultError:
                    sat = None
                solver.pop()
                if sat is False:
                    res.add(p)
                else:
                    keep.add(p)

        assert all(symb_is_curr(s) for p in res
                   for s in p.get_free_variables())
        assert all(self.cn(p) == p for p in res)
        assert all(self.cn(s) == s for s in keep)

        assert len(self.states) == len(self._u_trans)
        for c_state, c_trans in reversed(list(zip(self.states[1:],
                                                  self._u_trans))):
            keys = frozenset(k for k, v in c_trans.items()
                             if v.get_free_variables() <= self.symbs)
            c_preds = frozenset(res) | frozenset(c_state)
            c_state.clear()
            res = set()
            for p in c_preds:
                x_p = to_next(self.mgr, p, self.symbs)
                if x_p.get_free_variables() <= keys:
                    res.add(self.cn(self.simpl(self.subst(x_p, c_trans))))
                else:
                    c_state.add(p)

        assert all(symb_is_curr(s) for p in res
                   for s in p.get_free_variables())
        assert all(self.cn(s) == s for s in res)
        assert all(self.cn(s) == s for s in keep)
        return frozenset(res), frozenset(keep)

    def describe(self, param2val: dict, indent: str) -> str:
        assert isinstance(param2val, dict)
        assert isinstance(indent, str)
        assert all(p in param2val for p in self.parameters)

        ineqs = filter(lambda x: not x.is_true(),
                       (self.simpl(self.subst(ineq, param2val))
                        for ineq in self.first_ineqs))
        u_trans = [{u_s: self.simpl(self.subst(u_e, param2val))
                    for u_s, u_e in trans.items()}
                   for trans in self._u_trans]
        rf_ineq = self.simpl(self.subst(self._rf_pred, param2val))
        res = "{0}Do states {1}..{2} while {3}\n" \
              .format(indent, self.first, self.last, rf_ineq.serialize())
        for c_time in range(self.first, self.last + 1):
            idx = c_time - self.first
            res += "{}State {}\n".format(indent, c_time)
            for s, val in self.assigns[idx].items():
                res += "{}\t{} = {}\n".format(indent,
                                              s.serialize(), val.serialize())
            for s in self.states[idx]:
                res += "{}\t{}\n".format(indent,
                        self.simpl(self.subst(s, param2val)).serialize())
            if idx == 0:
                for ineq in ineqs:
                    res += "{}\t{}\n".format(indent, ineq.serialize())
            res += "{}Trans {} -- {}\n".format(indent, c_time,
                                               c_time + 1 if c_time < self.last
                                               else self.first)
            for s, expr in u_trans[idx].items():
                res += "{}\t{} : {}\n".format(indent, s.serialize(),
                                              expr.serialize())
        res += "{}End do-while\n".format(indent)
        return res

    def cfg(self, model) -> list:
        res = []
        for idx in range(len(self.states) - 1):
            res.append((self.first + idx + 1, frozenset()))
        rf_ineq = self.simpl(self.subst(self._rf_pred, model))
        res.append((self.first, rf_ineq))
        return res

    def to_smv(self, model, state_var, buf, expr_print) -> None:
        u_trans = [{u_s: self.simpl(self.subst(u_e, model))
                    for u_s, u_e in trans.items()}
                   for trans in self._u_trans]
        buf.write("\n-- RFFunnel\n")
        assert len(self.assigns) == len(u_trans)
        for idx, trans in enumerate(u_trans[:-1]):
            c_time = idx + self.first
            x_time = c_time + 1
            trans = self.mgr.And(self.mgr.Equals(k, v)
                                 for k, v in trans.items())
            buf.write("  -- transition from {} to {}\n".format(c_time,
                                                               x_time))
            buf.write("  TRANS ({0} = {1} & next({0}) = {2}) ->\n    (\n     "
                      .format(state_var, c_time, x_time))
            expr_print.printer(trans)
            buf.write("\n    );\n")
        trans = self.mgr.And(self.mgr.Equals(k, v)
                             for k, v in u_trans[-1].items())
        c_time = self.last
        x_time = self.first
        buf.write("  -- loop-back transition from {} to {}\n"
                  .format(c_time, x_time))
        buf.write("  TRANS ({0} = {1} & next({0}) = {2}) ->\n    (\n     "
                  .format(state_var, c_time, x_time))
        expr_print.printer(trans)
        buf.write("\n    );\n")

        buf.write("INVARSPEC NAME "
                  "RFFUN{0}_STATE_{0} := ({1} = {0} & next({1}) = {2}) -> "
                  .format(self.first, state_var, self.first + 1))
        invar = list(self.first_ineqs) + list(self.states[0])
        expr_print.printer(self.simpl(self.subst(self.mgr.And(invar), model)))
        buf.write(";\n")

        for idx, s in enumerate(self.states[1:]):
            s_idx = idx + 1 + self.first
            buf.write("INVARSPEC NAME RFFUN{2}_STATE_{0} := {1} = {0} -> "
                      .format(s_idx, state_var, self.first))
            expr_print.printer(self.simpl(self.subst(self.mgr.And(s), model)))
            buf.write(";\n")
        buf.write("INVARSPEC NAME "
                  "RFFUN{2}_STATE_{1}_EXIT := ({0} = {1} & next({0}) != {2}) -> "
                  .format(state_var, self.last, self.first))
        expr_print.printer(self.simpl(self.subst(self.mgr.And(self.last_ineqs),
                                                 model)))
        buf.write(";\n\n")
