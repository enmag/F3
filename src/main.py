from typing import FrozenSet, Set, Dict, List, Tuple, Iterator, Optional
from itertools import chain

from pysmt.environment import Environment as PysmtEnv
from pysmt.fnode import FNode
from pysmt.solvers.solver import Model
from pysmt.exceptions import SolverReturnedUnknownResultError

from trans_system import TransSystem
from hint import Hint
from bmc import BMC
from implicant import Implicant
from canonize import Canonizer
from floop import FLoopGen, FLoop
from rankfun import RankFun
from expr_at_time import ExprAtTime
from multisolver import MultiSolver
from expr_utils import (get_times, is_atom, assigns2fnodes, symb2next,
                        assign2fnode)
from utils import get_verbosity, log


_MAIN_LOG_LVL = 1


def get_log_lvl() -> int:
    return _MAIN_LOG_LVL


def set_log_lvl(val: int) -> None:
    assert isinstance(val, int)
    global _MAIN_LOG_LVL
    _MAIN_LOG_LVL = val


def search_floop(ts: TransSystem, fair: FNode,
                 hints: FrozenSet[Hint]) -> Optional[FLoop]:
    assert isinstance(ts, TransSystem)
    assert isinstance(ts.env, PysmtEnv)
    assert isinstance(fair, FNode)
    assert fair in ts.env.formula_manager.formulae.values()
    assert isinstance(hints, frozenset)
    assert all(isinstance(h, Hint) for h in hints)
    assert all(h.env == ts.env for h in hints)
    env = ts.env
    bmc = BMC(ts, fair, hints)
    impl = Implicant(env, bmc.cn)
    fgen = FLoopGen(env, bmc.totime, bmc.cn)
    rfs: Set[RankFun] = set()
    path_count = 0
    floop_count = 0
    while BMC.get_max_k() < 0 or bmc.k < BMC.get_max_k():
        curr = bmc.next()
        if curr is None:
            # try generate longer path.
            bmc.step()
            continue
        path_count += 1
        # bmc.k and lback correspond to the same abstract state.
        is_lasso, model, lback = curr
        assert isinstance(is_lasso, bool)
        assert isinstance(model, Model)
        assert isinstance(lback, int)
        assert 0 <= lback < bmc.k
        if __debug__:
            _mgr = env.formula_manager
            # no learned ranking function should decrease in loop.
            for rf in rfs:
                _fm = _mgr.And(rf.is_ranked(), rf.is_decr())
                _fm = bmc.totime(_fm, lback, bmc.k)
                assert model.get_value(_fm).is_false()
            # model satisfies unrolling.
            _prob = bmc.totime(_mgr.And(ts.init), 0)
            for _time in range(bmc.k):
                _prob = _mgr.And(_prob, bmc.totime(_mgr.And(ts.trans), _time))
            _prob = _mgr.And(_prob, bmc.totime(fair, bmc.k))
            assert model.get_value(_prob).is_true()
        if is_lasso is True:
            return fgen.make_lasso(ts.symbs, model, lback, bmc.k)
        assigns, regions, trans, h_symbs, h_regions, h_trans, h_rfs = \
            _loop_impl(bmc, fair, model, lback, impl)
        assert all(assigns[0].keys() == assign.keys() for assign in assigns[1:])
        trace = _model2trace(bmc.orig_ts.symbs, model, bmc.k, bmc.totime)
        del model
        _log_trace(env, trace, lback, bmc.k, bmc.totime,
                   path_count)
        # _log_candidate_loop(env, assigns, regions, trans, h_regions, h_trans,
        #                     h_rfs)
        floops: List[Tuple[int, FLoop]] = []
        log(f"\n\tGenerate candidate loops for path {path_count} "
            "and discard terminating.", get_log_lvl())
        remove_loop = True
        # compact reason for emptiness / possible unreachability of floop.
        interp: Optional[Tuple[int, Optional[FNode]]] = None
        # generate floops from most complex to simpler.
        for floop in fgen.gen(trace[lback:-1],
                              bmc.symbs - frozenset(assigns[0].keys()),
                              assigns, regions, trans, h_regions,
                              h_trans, h_rfs, rfs):
            assert interp is None
            floop_count += 1
            _log_floop(floop, floop_count)
            rf = floop.terminates(impl)
            if rf is None and len(floop.repl_constants(trace[-1])) > 0:
                rf = floop.terminates(impl)
            if rf is not None:
                assert rf not in rfs
                if not rf.is_trivial():
                    log(f"\tCandidate loop {floop_count} has ranking function: "
                        f"{rf}.", get_log_lvl())
                    if rf not in rfs:
                        remove_loop = False
                        bmc.refine_rf(rf)
                        rfs.add(rf)
                    break  # simpler floops share same rf.
                # unrealisable path.
                interp = floop.back_prop(impl)
                if interp is None:
                    interp = -1, None
                assert interp is not None

            if interp is None:
                interp = floop.back_prop(impl)
            if interp is not None:
                log(f"\tCandidate loop {floop_count} "
                    "unrealisable by predicate back-propagation in funnel "
                    f"{max(0, interp[0])}.", get_log_lvl())
            else:
                new_rfs = [rf for rf in floop.inst_inner_rfs(impl) - rfs
                           if not rf.is_trivial()]
                rfs.update(new_rfs)
                bmc.refine_rfs(new_rfs)
                interp = floop.rm_deadlocks(impl)
                if interp is not None:
                    log(f"\tCandidate loop {floop_count} empty by "
                        f"deadlock removal in funnel {max(0, interp[0])}; "
                        f"learn: {'' if interp[0] == -1 else env.serializer.serialize(interp[1])}.",
                        get_log_lvl())
                else:
                    interp = floop.rm_redundant_preds(impl)
                    if interp is not None:
                        log(f"\tCandidate loop {floop_count} unrealisable by "
                            f"redundant removal in funnel {max(0, interp[0])}; "
                            f"learn: {'' if interp[0] == -1 else env.serializer.serialize(interp[1])}.",
                            get_log_lvl())
            # itp is None: floop template can correspond to actual floop.
            # itp[0] == -1: no floop for template, no compact reason.
            # itp[0] >= 0: no floop for template, refine with itp[1].
            assert interp is None or interp[0] != -1 or interp[1] is None or \
                (isinstance(interp[0], int) and isinstance(interp[1], FNode) and
                 0 <= interp[0] < len(assigns))
            if interp is None:
                # floop template might correspond to some concrete floop.
                assert floop._check_first_state(impl) is None
                floops.append((floop_count, floop))
            else:
                if interp[0] == -1:
                    # -1 signals that floop is unrealisable, but no extra info.
                    interp = None
                assert interp is None or isinstance(interp, tuple)
                assert interp is None or len(interp) == 2
                assert interp is None or isinstance(interp[0], int)
                assert interp is None or 0 <= interp[0] < len(assigns)
                assert interp is None or isinstance(interp[1], FNode)
                assert interp is None or  \
                    interp[1] in env.formula_manager.formulae.values()
                break  # simpler floops "empty" for the same reason.

        # analyse floop templates from simpler to most complex.
        if len(floops) > 0:
            log("\tTry instantiate Funnel-Loop from remaining candidates for "
                f"path {path_count}", get_log_lvl())
            x_h_symbs = frozenset(symb2next(env, s) for s in h_symbs)
            for idx, floop_templ in reversed(floops):
                # introduce parametric expressions in transition relation.
                floop_templ.uapprox_trans(x_h_symbs)
                _log_floop(floop_templ, idx)
                # increasingly introduce predicates on regions.
                for num_ineqs, floop in floop_templ.uapprox_regs():
                    log(f"\tUsing {num_ineqs} parametric inequalities.",
                        get_log_lvl())
                    if floop.instantiate(impl):
                        return floop

        log("\tNo remaining candidates, generate next path.\n", get_log_lvl())
        # refine next candidates if we found some interpolants or
        # we have not discovered any ranking function.
        if interp is not None:
            assert 0 <= interp[0] < len(assigns)
            assert isinstance(interp[1], FNode)
            itps = [None for _ in assigns]
            itps[interp[0]] = interp[1]
            # admit generation of same candidate if one of interps holds.
            bmc.refine_loop([chain(assigns2fnodes(env, assign),
                                   reg, tr, h_reg, h_tr)
                             for assign, reg, tr, h_reg, h_tr in
                             zip(assigns, regions, trans,
                                 h_regions, h_trans)],
                            itps)
        elif remove_loop is True:
            if len(floops) > 0:
                # refine by removing most specific floop.
                bmc.refine_loop(list(floops[-1][1].candidate_steps(len(assigns))))
            # avoid generating same candidate loop until extra bmc unrolling.
            bmc.remove_loop_tmp([chain(assigns2fnodes(env, assign),
                                       reg, tr, h_reg, h_tr)
                                 for assign, reg, tr, h_reg, h_tr in
                                 zip(assigns, regions, trans,
                                     h_regions, h_trans)])

    return None


def _loop_impl(bmc: BMC, fair: FNode, model: Model, first: int,
               impl: Implicant) -> \
        Tuple[List[Dict[FNode, FNode]],
              List[Set[FNode]], List[Set[FNode]],
              FrozenSet[FNode],
              List[Set[FNode]], List[Set[FNode]],
              Dict[Tuple[int, int], RankFun]]:
    """Return implicant corresponding to trace model.
    Returns: <Assigns, Regions, Trans, Hint symbs, hint regs, hint trans, hint rfs>.
    Does not repeat lback: length = bmc.k - first."""
    assert model.get_value(bmc.totime(fair, bmc.k)).is_true()
    assert all(len(bmc.env.fvo.get_free_variables(p) & bmc.enc_symbs) == 0
               for p in bmc.orig_ts.trans)
    h_symbs, h_regions, h_assumes, h_trans, h_rfs = \
        bmc.hints_comp(model, first, bmc.k)
    assert len(h_regions) == len(h_assumes)
    assert len(h_regions) == len(h_trans)
    assert len(h_regions) == bmc.k - first
    if impl.get_merge_ineqs():
        for idx, (h_reg, h_tr) in enumerate(zip(h_regions, h_trans)):
            h_regions[idx] = impl.merge_ineqs(h_reg)
            h_trans[idx] = impl.merge_ineqs(h_tr)
    env = bmc.env
    cn = bmc.cn
    totime = bmc.totime

    def gen_fms(step: int, x_step: int) -> Iterator[FNode]:
        """Generate formula for which we want to find an implicant"""
        assert isinstance(step, int)
        assert isinstance(x_step, int)
        assert first <= step < x_step <= bmc.k
        yield from (cn(totime(pred, step)) for pred in bmc.orig_ts.trans)
        yield from (cn(totime(pred, x_step))
                    for pred in h_assumes[x_step - first if x_step < bmc.k
                                          else 0])
        if step == bmc.k - 1:
            yield cn(totime(fair, bmc.k))

    bool_symbs = bmc.fair_symbs | frozenset(s for s in bmc.symbs
                                            if s.symbol_type().is_bool_type())
    assert len(bool_symbs & bmc.enc_symbs) == 0
    true = env.formula_manager.TRUE()
    assigns: List[Dict[FNode, FNode]] = [dict() for _ in range(first, bmc.k)]
    regions: List[Set[FNode]] = [set() for _ in range(first, bmc.k)]
    trans: List[Set[FNode]] = [set() for _ in range(first, bmc.k)]

    for step, (h_reg, h_assume, h_t) in enumerate(zip(h_regions, h_assumes,
                                                      h_trans),
                                                  start=first):
        assert first <= step < bmc.k
        x_step = step + 1
        assume = {cn(totime(p, step)): true
                  for p in chain(h_reg, h_t, h_assume)}
        assume.update((cn(totime(p, x_step)), true)
                      for p in h_regions[x_step - first if x_step < bmc.k
                                         else 0])
        # assume assignments for boolean symbols.
        assume.update((s, model.get_value(s))
                      for s in (totime(s, step)
                                for s in bool_symbs))
        # add boolean symbols to assignments.
        assigns[step - first].update((s, model.get_value(t_s))
                                     for s, t_s in ((s, totime(s, step))
                                                    for s in bool_symbs))
        # assume assignments for next boolean symbols.
        assume.update((s, model.get_value(s))
                      for s in (totime(s, x_step)
                                for s in bool_symbs))
        # add each predicate to the corresponding region or trans
        for p in impl(gen_fms(step, x_step), model, assume):
            assert not p.is_true()
            assert not p.is_false()
            assert cn(p) == p
            assert is_atom(p)
            assert len(env.ao.get_atoms(p)) == 1
            assert len(env.fvo.get_free_variables(p)) >= 1
            assert model.get_value(p).is_true()
            is_next = get_times(env, p)
            assert len(is_next) in {1, 2}
            assert min(is_next) >= step
            assert max(is_next) <= step + 1
            c_time = min(is_next)
            idx = c_time - first
            p = cn(totime(p, -c_time - 1))
            assert len(get_times(env, p)) == 0
            assert cn(p) == p
            if len(is_next) == 1:
                assert len(regions) == bmc.k - first
                assert idx <= bmc.k - first
                regions[idx % (bmc.k - first)].add(p)
            else:
                assert len(is_next) == 2
                assert idx < bmc.k - first
                trans[idx].add(p)
    if impl.get_merge_ineqs():
        for idx, (reg, tr) in enumerate(zip(regions, trans)):
            regions[idx] = impl.merge_ineqs(reg)
            trans[idx] = impl.merge_ineqs(tr)
    assert len(regions) == bmc.k - first
    assert len(regions) == len(trans)
    assert len(regions) == len(assigns)
    assert len(regions) == len(h_regions)
    assert len(regions) == len(h_trans)
    assert all(s in (bmc.symbs | bmc.fair_symbs) for assign in assigns
               for s in assign)
    assert all(env.fvo.get_free_variables(p) <= bmc.symbs
               for reg in regions for p in reg)
    assert all(env.fvo.get_free_variables(p) <= bmc.symbs
               for reg in h_regions for p in reg)
    assert all(env.fvo.get_free_variables(p) <= bmc.symbs |
               frozenset(symb2next(env, s) for s in bmc.symbs)
               for tr in trans for p in tr)
    assert all(env.fvo.get_free_variables(p) <= bmc.symbs |
               frozenset(symb2next(env, s) for s in bmc.symbs)
               for tr in h_trans for p in tr)
    if __debug__:
        if impl.get_merge_ineqs():
            for idx, (reg, tr, h_reg, h_tr) in enumerate(zip(regions, trans,
                                                             h_regions, h_trans)):
                assert regions[idx] == impl.merge_ineqs(reg)
                assert trans[idx] == impl.merge_ineqs(tr)
                assert h_regions[idx] == impl.merge_ineqs(h_reg)
                assert h_trans[idx] == impl.merge_ineqs(h_tr)
        # trace is a model for regions and transitions
        assert all(model.get_value(totime(p, step)).is_true()
                   for step, preds in zip(range(first, bmc.k), regions)
                   for p in preds)
        assert all(model.get_value(totime(p, step)).is_true()
                   for step, preds in zip(range(first, bmc.k), trans)
                   for p in preds)
        assert all(model.get_value(totime(p, step)).is_true()
                   for step, preds in zip(range(first, bmc.k), h_regions)
                   for p in preds)
        assert all(model.get_value(totime(p, step)).is_true()
                   for step, preds in zip(range(first, bmc.k), h_trans)
                   for p in preds)
        # each step implies the transition relation.
        from expr_utils import to_next
        from solver import Solver
        mgr = env.formula_manager
        get_free_vars = env.fvo.get_free_variables
        for idx, _ in enumerate(regions):
            x_idx = (idx + 1) % len(regions)
            with Solver(env) as _solver:
                # add curr assign, region, h_region, h_assume, trans and h_trans
                _solver.add_assertions(assigns2fnodes(env, assigns[idx]))
                _solver.add_assertions(regions[idx])
                _solver.add_assertions(h_regions[idx])
                _solver.add_assertions(h_assumes[idx])
                _solver.add_assertions(trans[idx])
                _solver.add_assertions(h_trans[idx])
                # add next assign, region, h_region, h_assume
                _solver.add_assertions(to_next(env, p,
                                               bmc.symbs | bmc.enc_symbs |
                                               bmc.fair_symbs)
                                       for p in assigns2fnodes(env, assigns[x_idx]))
                _solver.add_assertions(to_next(env, p, bmc.symbs)
                                       for p in regions[x_idx])
                _solver.add_assertions(to_next(env, p, bmc.symbs)
                                       for p in h_regions[x_idx])
                _solver.add_assertions(to_next(env, p, bmc.symbs)
                                       for p in h_assumes[x_idx])
                _solver.push()
                # Is Sat.
                assert _solver.solve() is True
                # Implies transition rel.
                for _tr in bmc.orig_ts.trans:
                    if len(get_free_vars(_tr) & bmc.fair_symbs) == 0:
                        _solver.add_assertion(mgr.Not(_tr))
                        assert _solver.solve() is False
                        _solver.pop()
                        _solver.push()
    # end debug
    return assigns, regions, trans, h_symbs, h_regions, h_trans, h_rfs


def _constant_symbs(env: PysmtEnv,
                    symbs: FrozenSet[FNode],
                    trace: List[Dict[FNode, FNode]],
                    assigns: List[Dict[FNode, FNode]],
                    regs: List[FrozenSet[FNode]],
                    trans: List[FrozenSet[FNode]],
                    cn: Canonizer, totime: ExprAtTime) -> FrozenSet[FNode]:
    """Retrun subset of `symbs` that must follow a concrete lasso
    in the candidate loop."""
    assert isinstance(env, PysmtEnv)
    assert isinstance(symbs, frozenset)
    assert all(isinstance(s, FNode) for s in symbs)
    assert all(s in env.formula_manager.get_all_symbols() for s in symbs)
    assert all(s.symbol_type().is_real_type() or
               s.symbol_type().is_int_type() or
               s.symbol_type().is_bool_type()
               for s in symbs)
    assert isinstance(trace, list)
    assert isinstance(assigns, list)
    assert isinstance(regs, list)
    assert isinstance(trans, list)
    assert len(trace) == len(assigns) + 1
    assert len(assigns) == len(regs)
    assert len(assigns) == len(trans)
    assert all(isinstance(state, dict) for state in trace)
    assert all(isinstance(k, FNode) for state in trace for k in state)
    assert all(isinstance(v, FNode) for state in trace for v in state.values())
    assert all(k in env.formula_manager.get_all_symbols()
               for state in trace for k in state)
    assert all(v in env.formula_manager.formulae.values()
               for state in trace for v in state.values())
    assert all(env.stc.walk(s) == env.stc.walk(v)
               for state in trace for s, v in state.items())
    assert all(isinstance(state, dict) for state in assigns)
    assert all(isinstance(k, FNode) for state in assigns for k in state)
    assert all(isinstance(v, FNode) for state in assigns
               for v in state.values())
    assert all(k in env.formula_manager.get_all_symbols()
               for state in assigns for k in state)
    assert all(v in env.formula_manager.formulae.values()
               for state in assigns for v in state.values())
    assert all(env.stc.walk(s) == env.stc.walk(v)
               for state in assigns for s, v in state.items())
    assert all(isinstance(ps, frozenset) for ps in chain(regs, trans))
    assert all(isinstance(p, FNode) for ps in chain(regs, trans) for p in ps)
    assert all(p in env.formula_manager.formulae.values()
               for ps in chain(regs, trans) for p in ps)
    assert all(cn(p) == p for ps in chain(regs, trans) for p in ps)
    assert isinstance(totime, ExprAtTime)
    assert totime.env == env
    assert isinstance(cn, Canonizer)
    assert cn.env == env

    mgr = env.formula_manager
    # integer or real -valued symbs that can correspond to lasso.
    symbs = frozenset(s for s in symbs if trace[0][s] == trace[-1][s] and
                      (s.symbol_type().is_int_type() or
                      s.symbol_type().is_real_type()))
    res = []
    to_analyse = []
    for s in symbs:
        eq = cn(mgr.Equals(symb2next(env, s), s))
        if all(eq in tr for tr in trans):
            res.append(s)
        else:
            to_analyse.append(s)

    if len(to_analyse) > 0:
        # regs
        assertions = [totime(pred, idx)
                      for idx, reg in enumerate(regs)
                      for pred in reg]
        # abst_trans & hint_trans
        assertions.extend(totime(pred, idx)
                          for idx, tr in enumerate(trans)
                          for pred in tr)
        # add assignments we already discovered.
        assertions.extend(assign2fnode(env, totime(s, idx), step[s])
                          for idx, step in enumerate(trace)
                          for s in res)
        assert all(isinstance(p, FNode) for p in assertions)
        with MultiSolver(env, get_const_symbs_timeout(),
                         log_lvl=get_log_lvl() + 1) as solver:
            solver.add_assertions(assertions)
            solver.push()
            while to_analyse:
                s = to_analyse.pop()
                # unsat (states & trans & s_0 = v_0 & !(/\ s_i = v_i))
                solver.add_assertion(mgr.Equals(totime(s, 0),
                                                trace[0][s]))
                solver.add_assertion(mgr.Not(mgr.And(
                    mgr.Equals(totime(s, idx + 1), x_step[s])
                    for idx, x_step in enumerate(trace[1:]))))
                try:
                    sat = solver.solve()
                except SolverReturnedUnknownResultError:
                    sat = None
                    solver.reset_assertions()
                    solver.add_assertions(assertions)
                    solver.push()
                solver.pop()
                if sat is False:
                    res.add(s)
                    for idx, step in enumerate(trace):
                        eq = mgr.Equals(totime(s, idx), step[s])
                        solver.add_assertion(eq)
                        assertions.append(eq)
                solver.push()

    if __debug__:
        from solver import Solver
        # check validity of constant symbs.
        with Solver(env=env) as _solver:
            # abst_states & hint_states
            for idx, state in enumerate(regs):
                c_time = idx
                for pred in state:
                    assert isinstance(pred, FNode)
                    _solver.add_assertion(totime(pred, c_time))
            for idx, tr in enumerate(trans):
                c_time = idx
                for pred in tr:
                    _solver.add_assertion(totime(pred, c_time))
            for s in res:
                _solver.add_assertion(assign2fnode(env, totime(s, 0),
                                                   trace[0][s]))
            disj = []
            for idx, x_step in enumerate(trace[1:]):
                for s in res:
                    eq = assign2fnode(env, totime(s, idx + 1),
                                      x_step[s])
                    disj.append(eq)
            _solver.add_assertion(mgr.Not(mgr.And(disj)))
            assert _solver.solve() is False

    return frozenset(res)


def _model2trace(symbs: FrozenSet[FNode], model: Model, last: int,
                 totime: ExprAtTime) -> List[Dict[FNode, FNode]]:
    assert isinstance(symbs, (set, frozenset))
    assert all(isinstance(s, FNode) for s in symbs)
    assert hasattr(model, "get_value")
    assert isinstance(last, int)
    assert last > 0
    assert isinstance(totime, ExprAtTime)
    assert all(s in totime.env.formula_manager.get_all_symbols()
               for s in symbs)
    return [{s: model.get_value(totime(s, t))
             for s in symbs} for t in range(last + 1)]

def _log_trace(env: PysmtEnv,
               trace: List[Dict[FNode, FNode]],
               lback: int, last: int, totime: ExprAtTime,
               idx: int) -> None:
    assert isinstance(env, PysmtEnv)
    assert isinstance(trace, list)
    assert len(trace) == last + 1
    assert all(isinstance(state, dict) for state in trace)
    assert all(s in env.formula_manager.get_all_symbols()
               for state in trace for s in state)
    assert all(v in env.formula_manager.formulae.values()
               for state in trace for v in state.values())
    assert all(v.is_constant() for state in trace
               for v in state.values())
    assert all(frozenset(trace[0].keys()) == frozenset(step.keys())
               for step in trace)
    assert isinstance(lback, int)
    assert 0 <= lback < last
    assert isinstance(last, int)
    assert isinstance(totime, ExprAtTime)
    assert totime.env == env
    assert isinstance(idx, int)
    if get_log_lvl() > get_verbosity():
        return
    serialize = env.serializer.serialize
    symbs = sorted(trace[0].keys(), key=lambda s: s.symbol_name())
    log(f"\tTrace {idx}: lback {lback}, length {last + 1};", get_log_lvl())
    for t, state in enumerate(trace):
        log(f"\tState {t}", get_log_lvl())
        log("\n".join(f"\t\t{serialize(s)}: {serialize(state[s])}"
                      for s in symbs),
            get_log_lvl())

def _log_candidate_loop(env: PysmtEnv,
                        assigns: List[Dict[FNode, FNode]],
                        regs: List[Set[FNode]],
                        trans: List[Set[FNode]],
                        h_regs: List[Set[FNode]],
                        h_trans: List[Set[FNode]],
                        h_rfs: Dict[Tuple[int, int], RankFun]) -> None:
    assert isinstance(env, PysmtEnv)
    assert isinstance(assigns, list)
    assert all(isinstance(state, dict) for state in assigns)
    assert all(frozenset(state.keys()) <=
               frozenset(env.formula_manager.get_all_symbols())
               for state in assigns)
    assert all(frozenset(state.values()) <=
               frozenset(env.formula_manager.formulae.values())
               for state in assigns)
    assert isinstance(regs, list)
    assert all(isinstance(reg, (set, frozenset)) for reg in regs)
    assert all(reg <= frozenset(env.formula_manager.formulae.values())
               for reg in regs)
    assert isinstance(trans, list)
    assert all(isinstance(tr, (set, frozenset)) for tr in trans)
    assert all(tr <= frozenset(env.formula_manager.formulae.values())
               for tr in trans)
    assert isinstance(h_regs, list)
    assert all(isinstance(reg, (set, frozenset)) for reg in h_regs)
    assert all(reg <= frozenset(env.formula_manager.formulae.values())
               for reg in h_regs)
    assert isinstance(h_trans, list)
    assert all(isinstance(tr, (set, frozenset)) for tr in h_trans)
    assert all(tr <= frozenset(env.formula_manager.formulae.values())
               for tr in h_trans)
    assert isinstance(h_rfs, dict)
    assert all(isinstance(k, tuple) for k in h_rfs)
    assert all(len(k) == 2 for k in h_rfs)
    assert all(isinstance(k[0], int) and isinstance(k[1], int)
               for k in h_rfs)
    assert len(assigns) == len(regs)
    assert len(regs) == len(trans)
    assert len(regs) == len(h_regs)
    assert len(regs) == len(h_trans)
    assert all(isinstance(rf, RankFun) for rf in h_rfs.values())
    if get_log_lvl() > get_verbosity():
        return
    serialize = env.serializer.serialize
    log("\n\tCandidate loop", get_log_lvl())
    for idx, (state, reg, h_reg, tr, h_tr) in enumerate(
            zip(assigns, regs, h_regs, trans, h_trans)):
        log(f"\tRegion {idx}", get_log_lvl())
        log("\n".join(f"\t\t{serialize(s)} := {serialize(state[s])}"
                      for s in sorted(state.keys(),
                                      key=lambda s: s.symbol_name())))
        log("\n".join(f"\t\t{serialize(p)}" for p in reg),
            get_log_lvl())
        log("\n".join(f"\t\t{serialize(p)}\t(hint)" for p in h_reg),
            get_log_lvl())
        log(f"\tTransition {idx} -- {idx + 1}", get_log_lvl())
        log("\n".join(f"\t\t{serialize(p)}" for p in tr),
            get_log_lvl())
        log("\n".join(f"\t\t{serialize(p)}\t(hint)" for p in h_tr),
            get_log_lvl())


def _log_floop(floop: FLoop, num) -> None:
    assert isinstance(floop, FLoop)
    if get_log_lvl() > get_verbosity():
        return
    log(f"\n\tCandidate loop {num}:\n{floop}", get_log_lvl())
