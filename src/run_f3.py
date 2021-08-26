#! /usr/bin/env python3
# -*- coding: utf-8 -*-
from typing import Optional, FrozenSet
import os
import time
import argparse
from itertools import chain
from importlib.util import spec_from_file_location, module_from_spec

from pysmt.environment import Environment as PysmtEnv
from pysmt.fnode import FNode

from ltl.ltl import LTLEncoder, Options

from abstract_loops import BMC, HintMode
from main import (search_funnel_bmc, set_use_ef, get_use_ef,
                  set_use_motzkin, get_use_motzkin,
                  set_use_ef_rf, get_use_ef_rf,
                  set_use_motzkin_rf, get_use_motzkin_rf,
                  set_rf_learn_ef, get_rf_learn_ef,
                  set_fun_learn_ef, get_fun_learn_ef,
                  get_use_generalised_lasso, set_use_generalised_lasso)
from ranker import Ranker
from solver import Solver, set_solvers, set_solver_name
from smv_printer import ltl_to_smv
from encode_diverging import encode_diverging, set_div_mode, get_div_mode
from generalise import Generaliser
from funnel import FunnelLoop
from hint import Hint
from efsolver import (set_timeout as efsolver_timeout,
                      get_timeout as efsolver_get_timeout,
                      set_maxloops as efsolver_max_loops,
                      get_maxloops as efsolver_get_max_loops,
                      get_ef_approximate, set_ef_approximate)
from rationalapprox import (get_approx_precision, set_approx_precision,
                            get_val_bound as approx_get_val_bound,
                            set_val_bound as approx_set_val_bound)

from utils import (log, symb_to_next, symb_is_curr, symb_to_curr,
                   set_verbosity, get_verbosity)


if __debug__:
    import faulthandler
    faulthandler.enable()

_CHECK_HINTS = False


def get_check_hints() -> bool:
    global _CHECK_HINTS
    return _CHECK_HINTS


def set_check_hints(val: bool) -> None:
    assert isinstance(val, bool)
    global _CHECK_HINTS
    _CHECK_HINTS = val


def run_ltl_test(test, env: PysmtEnv, label: str, out_dir=None) -> bool:
    assert hasattr(test, "check_ltl")
    assert callable(test.check_ltl)
    assert isinstance(env, PysmtEnv)
    mgr = env.formula_manager
    get_free_vars = env.fvo.walk
    _LOG_LVL = 0
    with Solver(env=env, name="msat",
                solver_options={'allow_bool_function_args': 'true'}) as solver:
        menv = solver.msat_env()
        convert = solver.converter.back
        opts = Options()
        opts.ltl_single_fairness_sorted = False
        enc = LTLEncoder(opts, menv)
        ok = enc.init()
        assert ok
        msat_symbs, msat_init, msat_trans, msat_ltl = test.check_ltl(menv, enc)

        if hasattr(test, "diverging_symbs"):
            assert callable(test.diverging_symbs)
            div_symbs = test.diverging_symbs(menv)
            assert all(div_s in msat_symbs.keys() for div_s in div_symbs)
            for div_s in div_symbs:
                msat_symbs, msat_init, msat_trans, msat_ltl = \
                    encode_diverging(menv, enc, div_s,
                                     msat_symbs, msat_init,
                                     msat_trans, msat_ltl)
        # product construction.
        ts = enc.encode(msat_symbs, msat_ltl)
        assert all(symb_to_next(mgr, convert(s)) == convert(x_s)
                   for s, x_s in msat_symbs.items())

        ltl_str = ltl_to_smv(env, solver, enc, msat_ltl) if out_dir else None
        orig_trans = convert(msat_trans)
        init = mgr.And(convert(msat_init), convert(ts.init()))
        trans = mgr.And(orig_trans, convert(ts.trans()))
        fairness = mgr.Not(convert(ts.prop()))
    assert all(symb_is_curr(s) for s in get_free_vars(init))
    assert all(symb_is_curr(s) for s in get_free_vars(fairness))
    symbols = frozenset(chain(get_free_vars(init), get_free_vars(fairness),
                              (s if symb_is_curr(s) else symb_to_curr(mgr, s)
                               for s in get_free_vars(trans))))
    assert all(symb_is_curr(s) for s in symbols)
    assert get_free_vars(init) <= symbols
    assert get_free_vars(fairness) <= symbols
    assert get_free_vars(trans) <= symbols | \
        frozenset(symb_to_next(mgr, s) for s in symbols)
    assert ts.live_prop()

    if hasattr(test, "hints"):
        assert callable(test.hints)
        hints = test.hints(env)
        assert isinstance(hints, frozenset)
        assert all(isinstance(h, Hint) for h in hints)
        if get_check_hints():
            for h in hints:
                correct, msgs = h.is_correct()
                if correct is not True:
                    log(f"{'ERROR' if correct is False else 'UNKNOWN'}"
                        "\n".join(msgs), 0)
                if correct is False:
                    return False
        for h in hints:
            symbols |= h.all_symbs
    else:
        hints = frozenset([])

    return search_nonterm(env, symbols, init, trans, fairness,
                          hints, label, _LOG_LVL, out_dir,
                          orig_trans=orig_trans,
                          orig_ltl=ltl_str)


def run_test(test, env: PysmtEnv, label: str, out_dir=None) -> bool:
    assert hasattr(test, "transition_system")
    assert callable(test.transition_system)
    assert isinstance(env, PysmtEnv)
    _LOG_LVL = 0
    symbols, init, trans, fairness = test.transition_system(env)
    assert isinstance(symbols, frozenset)
    assert isinstance(init, FNode)
    assert isinstance(trans, FNode)
    assert isinstance(fairness, FNode)
    if hasattr(test, "hints"):
        assert callable(test.hints)
        hints = test.hints(env)
        assert isinstance(hints, frozenset)
        assert all(isinstance(h, Hint) for h in hints)
        if get_check_hints():
            for h in hints:
                correct, msgs = h.is_correct()
                if correct is not True:
                    log(f"{'ERROR' if correct is False else 'UNKNOWN'}"
                        "\n".join(msgs), 0)
                if correct is False:
                    return False
        for h in hints:
            symbols |= h.all_symbs

    else:
        hints = frozenset([])

    return search_nonterm(env, symbols, init, trans, fairness,
                          hints, label, _LOG_LVL, out_dir)


def search_nonterm(env, symbols: FrozenSet[FNode],
                   init: FNode, trans: FNode, fairness: FNode,
                   hints: FrozenSet[Hint],
                   label: str, _LOG_LVL: int,
                   out_dir=None, orig_trans=None,
                   orig_ltl: Optional[str] = None) -> bool:
    assert isinstance(symbols, frozenset)
    assert isinstance(init, FNode)
    assert isinstance(trans, FNode)
    assert isinstance(fairness, FNode)
    assert isinstance(hints, frozenset)
    assert all(isinstance(h, Hint) for h in hints)
    assert isinstance(label, str)
    assert isinstance(_LOG_LVL, int)
    serialize = env.serializer.serialize
    log(f"\tinit: {serialize(init)}", _LOG_LVL+1)
    log(f"\ttrans: {serialize(trans)}", _LOG_LVL+1)
    log(f"\tfairness: {serialize(fairness)}", _LOG_LVL+1)
    log(f"\thints: {', '.join(str(h) for h in hints)}\n", _LOG_LVL+1)
    _, arg0, arg1 = search_funnel_bmc(env, symbols, init, trans,
                                      fairness, hints)
    success = False
    if arg0 is not None:
        if isinstance(arg0, frozenset):
            assert isinstance(arg1, frozenset)
            log("\n\tFound non-termination argument based on generalised lasso:\n"
                f"\tpos diverging vars: {arg0};\n\tneg diverging vars: {arg1};",
                _LOG_LVL)
        else:
            if arg1 is None:
                nonterm = "".join(f"\t{', '.join(f'{serialize(k)} : {serialize(v)}' for k, v in eqs.items())}\n"
                                  for eqs in arg0)
            else:
                nonterm = arg0.describe(arg1, indent='\t')
            log(f"\n\tFound non-termination argument:\n{nonterm}",
                _LOG_LVL)
        success = True
    else:
        log("\n\tFailed to synth non-termination argument\n", _LOG_LVL)
    if out_dir and arg1 is not None:
        out_f = os.path.join(out_dir, f"{label}.smv")
        with open(out_f, "w") as out:
            if orig_trans is None:
                orig_trans = trans
            arg.to_smv(orig_trans, fairness, arg1, out,
                       orig_ltl=orig_ltl)
    return success


def set_options(opts):
    set_verbosity(opts.verbose)

    set_use_ef_rf(bool(opts.use_ef_rf))
    Ranker.set_timeout(opts.synth_rf_motzkin_timeout)
    Ranker.set_approximate(bool(opts.rank_approx_model))
    set_use_motzkin_rf(bool(opts.use_motzkin_rf))
    set_use_motzkin(bool(opts.use_motzkin))
    set_rf_learn_ef(bool(opts.rf_learn_ef))
    set_fun_learn_ef(bool(opts.fun_learn_ef))
    FunnelLoop.set_timeout(opts.motzkin_timeout)
    FunnelLoop.set_min_ineqs(opts.min_inequalities)
    FunnelLoop.set_max_ineqs(opts.max_inequalities)
    FunnelLoop.set_propagate_mode(opts.propagate_mode)

    BMC.set_timeout(opts.bmc_timeout)
    BMC.set_max_k(opts.bmc_length)
    BMC.set_hints_mode(HintMode(opts.hint_mode))
    Generaliser.set_use_bool_impl(bool(opts.use_bool_impl))
    Generaliser.set_use_unsat_cores(bool(opts.use_unsat_cores))
    Generaliser.set_minimal_core(bool(opts.minimal_core))
    Generaliser.set_merge_ineqs(bool(opts.merge_ineqs))

    set_use_ef(bool(opts.use_ef))
    efsolver_timeout(opts.efsolver_timeout)
    efsolver_max_loops(opts.efsolver_iterations)
    set_ef_approximate(bool(opts.ef_approx_model))

    set_use_generalised_lasso(bool(opts.generalised_lasso))
    set_div_mode(bool(opts.deterministic_diverging_monitor))
    approx_set_val_bound(opts.approx_max_val)
    set_approx_precision(opts.approx_precision)

    set_solvers(opts.solvers)
    set_solver_name(opts.solvers[0])

    set_check_hints(bool(opts.check_hints))


def load_problem(test_file):
    test_spec = spec_from_file_location("test", test_file)
    test_module = module_from_spec(test_spec)
    test_spec.loader.exec_module(test_module)
    return test_module


def solve_problem(problem, label: str, out_dir) -> Optional[bool]:
    assert isinstance(label, str)
    assert not (hasattr(problem, "transition_system") and
                hasattr(problem, "check_ltl"))
    env = PysmtEnv()
    if hasattr(problem, "transition_system"):
        return run_test(problem, env, label, out_dir)
    assert hasattr(problem, "check_ltl")
    return run_ltl_test(problem, env, label, out_dir)


def run_f3(benchmark: str, out_dir):
    assert benchmark.endswith(".py")
    label = os.path.basename(benchmark)[:-3]
    log(f"F3 run `{label}`", 0)
    start = time.time()
    prob = load_problem(benchmark)
    res = solve_problem(prob, label, out_dir)
    runtime = time.time() - start
    log(f"end of `{label}`: "
        f"{'SUCCESS' if res is True else 'FAILURE' if res is False else 'UNKNOWN'}"
        f" in {runtime}s", 0)


def config_args():
    p = argparse.ArgumentParser()
    p.add_argument("benchmark", type=str,
                   help="python file describing the problem to be solved.")

    approx = p.add_argument_group("Constant simplifications")
    approx.add_argument('-approx-prec', '--approx-precision', type=int,
                        default=get_approx_precision(),
                        help="precision of approximation of rational values "
                        "to simplify constants in models. "
                        f"({get_approx_precision()})")
    approx.add_argument('-approx-max-val', '--approx-max-val', type=int,
                        default=approx_get_val_bound(),
                        help="try to keep constants below given number. "
                        f"({approx_get_val_bound()})")

    bmc = p.add_argument_group("Bounded Model Checking")
    bmc.add_argument('-bmc-t', '--bmc-timeout', type=int,
                     default=BMC.get_timeout(),
                     help="set timeout for each BMC SMT query. "
                     f"({BMC.get_timeout()}s)")
    bmc.add_argument('-bmc-k', '--bmc-length', type=int,
                     default=BMC.get_max_k(),
                     help="set max BMC unrolling, 0 or negative for unbounded. "
                     f"({BMC.get_max_k()})")
    bmc.add_argument('-h-mode', '--hint-mode', type=int,
                     default=int(BMC.get_hints_mode()),
                     choices=list(map(int, HintMode)),
                     help="type of hint choice encoding; "
                     "0: may enable; 1: must enable at least 1; "
                     "2: must enable all. "
                     f"({int(BMC.get_hints_mode())})")

    ef = p.add_argument_group("Exists-Forall solver")
    ef.add_argument('-ef-t', '--efsolver-timeout', type=int,
                    default=efsolver_get_timeout(),
                    help="set timeout for each SMT query in EF-solver. "
                    f"({efsolver_get_timeout()}s)")
    ef.add_argument('-ef-its', '--efsolver-iterations', type=int,
                    default=efsolver_get_max_loops(),
                    help="set max number of iteration in EF-solver. "
                    f"({efsolver_get_max_loops()})")
    ef.add_argument('-ef-approx', '--ef-approx-model', type=int,
                    default=int(get_ef_approximate()),
                    choices=[0, 1],
                    help="try simplify constants in EF-models. "
                    f"({int(get_ef_approximate())})")

    fun = p.add_argument_group("Funnel")
    fun.add_argument('-motzkin', '--use-motzkin', type=int,
                     default=int(get_use_motzkin()),
                     choices=[0, 1],
                     help="use motzkin transposition to solve EF quantified "
                     f"queries. ({int(get_use_motzkin())})")
    fun.add_argument('-motzkin-t', '--motzkin-timeout', type=int,
                     default=FunnelLoop.get_timeout(),
                     help="set timeout for each Motzkin-generated "
                     f"SMT query. ({FunnelLoop.get_timeout()}s)")
    fun.add_argument('-fun-learn-ef', '--fun-learn-ef', type=int,
                     default=int(get_fun_learn_ef()),
                     choices=[0, 1],
                     help="add constraints learned by EF-solver to "
                     "motzkin SMT-query in Funnel synthesis. "
                     f"({int(get_fun_learn_ef())})")
    fun.add_argument('-ef', '--use-ef', type=int, default=int(get_use_ef()),
                     help="use EF-solver for EF quantified queries. "
                     f"({int(get_use_ef())})")
    fun.add_argument('-min-ineqs', '--min-inequalities', type=int,
                     default=FunnelLoop.get_min_ineqs(),
                     help="set minimum number of inequalities in nontermination "
                     f"argument. ({FunnelLoop.get_min_ineqs()})")
    fun.add_argument('-max-ineqs', '--max-inequalities', type=int,
                     default=FunnelLoop.get_max_ineqs(),
                     help="set max number of inequalities in nontermination "
                     f"argument. ({FunnelLoop.get_max_ineqs()})")
    fun.add_argument('-propagate', '--propagate-mode', type=int,
                     default=int(FunnelLoop.get_propagate_mode()),
                     choices=[0, 1, 2],
                     help="backward propagate constraints in Funnels "
                     "0: no; 1: partial; 2: full. "
                     f"({FunnelLoop.get_propagate_mode()})")
    fun.add_argument('-propagate-max-it', '--propagate-max-iterations', type=int,
                     default=int(FunnelLoop.get_propagate_max_it()),
                     help="max number of backward propagations. "
                     f"({FunnelLoop.get_propagate_max_it()})")

    impl = p.add_argument_group("Implicant")
    impl.add_argument('-bool-impl', '--use-bool-impl', type=int,
                      default=int(Generaliser.get_use_bool_impl()),
                      choices=[0, 1],
                      help="compute model-based boolean implicant to generalise "
                      f"path. ({int(Generaliser.get_use_bool_impl())})")
    impl.add_argument('-unsat-cores', '--use-unsat-cores', type=int,
                      default=int(Generaliser.get_use_unsat_cores()),
                      choices=[0, 1],
                      help="use unsat-cores to generalise path. "
                      f"({int(Generaliser.get_use_unsat_cores())})")
    impl.add_argument('-min-core', '--minimal-core', type=int,
                      default=int(Generaliser.get_minimal_core()),
                      choices=[0, 1],
                      help="shrink unsat-core to obtain a minimal one w.r.t inequalities. "
                      f"({int(Generaliser.get_minimal_core())})")
    impl.add_argument('-merge-ineqs', '--merge-ineqs', type=int,
                      default=int(Generaliser.get_merge_ineqs()),
                      choices=[0, 1],
                      help="merge a <= b & b >= a into a = b "
                      "during path generalisation. "
                      f"({int(Generaliser.get_merge_ineqs())})")

    rank = p.add_argument_group("Ranking function")
    rank.add_argument('-rf-motzkin-t', '--synth-rf-motzkin-timeout', type=int,
                      default=Ranker.get_timeout(),
                      help="set timeout for Motzkin SMT queries for RF synthesis. "
                      f"({Ranker.get_timeout()}s)")
    rank.add_argument('-motzkin-rf', '--use-motzkin-rf', type=int,
                      default=int(get_use_motzkin_rf()),
                      choices=[0, 1],
                      help="use motzkin transposition to solve EF quantified "
                      "queries for ranking function. "
                      f"({int(get_use_motzkin_rf())})")
    rank.add_argument('-rank-approx', '--rank-approx-model', type=int,
                      default=int(Ranker.get_approximate()),
                      choices=[0, 1],
                      help="try simplify parameter assignments for ranking functions. "
                      f"({int(Ranker.get_approximate())})")
    rank.add_argument('-rf-learn-ef', '--rf-learn-ef', type=int,
                      default=int(get_rf_learn_ef()),
                      choices=[0, 1],
                      help="add constraints learned by EF-solver to "
                      "motzkin SMT-query in Ranking Function synthesis. "
                      f"({int(get_rf_learn_ef())})")
    rank.add_argument('-ef-rf', '--use-ef-rf', type=int,
                      default=int(get_use_ef_rf()),
                      choices=[0, 1],
                      help="use EF-solver for EF quantified queries for "
                      f"Ranking Funciton. ({int(get_use_ef_rf())})")

    other = p.add_argument_group("Other")
    other.add_argument('-v', '--verbose', type=int, default=get_verbosity(),
                       help=f"set verbosity level. ({get_verbosity()})")
    other.add_argument('-s', '--solvers', type=str, nargs='+',
                       default=["msat", "z3"],
                       help="set list of available solvers, "
                       "see `pysmt-install --check`.")
    other.add_argument('-generalised-lasso', '--generalised-lasso', type=int,
                       default=int(get_use_generalised_lasso()),
                       choices=[0, 1],
                       help="enable/disable detection of generalised lasso using "
                       "pattern described in Timed-nuXmv paper CAV 2019. "
                       f"({int(get_use_generalised_lasso())})")
    other.add_argument('-det-div', '--deterministic-diverging-monitor', type=int,
                       default=int(get_div_mode()),
                       choices=[0, 1],
                       help="1: use deterministic diverging monitor, "
                       "0: use nondeterministic reset for diverging monitor. "
                       f"({int(get_div_mode())})")
    other.add_argument('-smv-out', '--smv-out', type=str, default=None,
                       help="write smv representation of nontermination argument "
                       "in the given directory.")
    other.add_argument('-check-h', '--check-hints', type=int,
                       default=int(get_check_hints()),
                       choices=[0, 1],
                       help="1: check hints correctness, "
                       "0: assume hints are correct. "
                       f"({int(get_check_hints())})")
    return p


def main(opts):
    # make sure methods in Pysmt do not use global environment.
    from pysmt.environment import pop_env
    pop_env()
    if __debug__:
        from pysmt.environment import ENVIRONMENTS_STACK
        assert len(ENVIRONMENTS_STACK) == 0

    bench = opts.benchmark
    out_dir = opts.smv_out
    set_options(opts)
    run_f3(bench, out_dir)


if __name__ == "__main__":
    main(config_args().parse_args())
