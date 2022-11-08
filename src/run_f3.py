#! /usr/bin/env python3
# -*- coding: utf-8 -*-
from typing import Optional, FrozenSet
from os.path import join as path_join, basename as path_basename
import time
import argparse
from itertools import chain
from importlib.util import spec_from_file_location, module_from_spec

from pysmt.environment import Environment as PysmtEnv
from pysmt.fnode import FNode

from ltl.ltl import LTLEncoder, Options

from bmc import BMC, HintMode
from main import search_floop
from trans_system import TransSystem
from hint import Hint
from floop import FLoopGen, FLoop, Funnel
from solver import Solver, set_solvers, set_solver_name
from smv_printer import ltl_to_smv
from encode_diverging import encode_diverging, set_div_mode, get_div_mode
from implicant import Implicant
from efsolver import (set_timeout as efsolver_timeout,
                      get_timeout as efsolver_get_timeout,
                      set_maxloops as efsolver_max_loops,
                      get_maxloops as efsolver_get_max_loops,
                      get_ef_approximate, set_ef_approximate)
from motzkin import (get_timeout as motzkin_get_timeout,
                     set_timeout as motzkin_set_timeout,
                     get_motzkin_approximate, set_motzkin_approximate)
from rationalapprox import (get_approx_precision, set_approx_precision,
                            get_val_bound as approx_get_val_bound,
                            set_val_bound as approx_set_val_bound)
from expr_utils import symb2next, symb_is_curr, symb2curr
from utils import log, set_verbosity, get_verbosity


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


def run_ltl_test(test, env: PysmtEnv, label: str,
                 out_dir: Optional[str]) -> Optional[bool]:
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
        msat_symbs, init, trans, ltl = test.check_ltl(menv, enc)
        init = convert(init)
        orig_trans = convert(trans)
        ts = TransSystem(env, frozenset(convert(s) for s in msat_symbs),
                         init, orig_trans)
        if hasattr(test, "diverging_symbs"):
            from mathsat import msat_make_and, msat_make_not, msat_make_or
            assert callable(test.diverging_symbs)
            div_symbs = test.diverging_symbs(menv)
            assert all(div_s in msat_symbs.keys() for div_s in div_symbs)
            div_ltls = None
            for div_s in div_symbs:
                new_s, init, trans, div_ltl = \
                    encode_diverging(menv, enc, div_s, msat_symbs)
                ts.add_symb(convert(new_s))
                ts.add_init(convert(init))
                ts.add_trans(convert(trans))
                div_ltls = div_ltl if div_ltls is None \
                    else msat_make_and(menv, div_ltls, div_ltl)
            ltl = msat_make_or(menv, msat_make_not(menv, div_ltls), ltl)
        # product construction.
        ltl_ts = enc.encode(msat_symbs, ltl)
        assert all(symb2next(env, convert(s)) == convert(x_s)
                   for s, x_s in msat_symbs.items())
        ltl_str = ltl_to_smv(env, solver, enc, ltl) if out_dir else None
        init = convert(ltl_ts.init())
        trans = convert(ltl_ts.trans())
        fairness = mgr.Not(convert(ltl_ts.prop()))
        ts.prod(TransSystem(env,
                            frozenset(convert(s) for s in ltl_ts.statevars()),
                            init, trans))
    assert all(symb_is_curr(s) for pred in ts.init for s in get_free_vars(pred))
    assert all(symb_is_curr(s) for s in get_free_vars(fairness))
    assert ts.symbs <= frozenset(chain((s for pred in ts.init
                                        for s in get_free_vars(pred)),
                                       get_free_vars(fairness),
                                       (s if symb_is_curr(s) else
                                        symb2curr(env, s)
                                        for pred in ts.trans
                                        for s in get_free_vars(pred))))
    assert all(symb_is_curr(s) for s in ts.symbs)
    assert all(get_free_vars(pred) <= ts.symbs for pred in ts.init)
    assert get_free_vars(fairness) <= ts.symbs
    assert all(get_free_vars(pred) <= ts.symbs |
               frozenset(symb2next(env, s) for s in ts.symbs)
               for pred in ts.trans)
    assert ltl_ts.live_prop()

    if hasattr(test, "hints"):
        assert callable(test.hints)
        hints = test.hints(env)
        assert isinstance(hints, frozenset)
        assert all(isinstance(h, Hint) for h in hints)
        if get_check_hints():
            for h in hints:
                correct, msgs = h.is_correct()
                if correct is not True:
                    log("\n".join(msgs), 0)
                if correct is False:
                    return False
    else:
        hints = frozenset([])

    return search_nonterm(ts, fairness, hints, label,
                          _LOG_LVL, out_dir,
                          orig_trans=orig_trans,
                          orig_ltl=ltl_str)


def run_test(test, env: PysmtEnv, label: str,
             out_dir: Optional[str]) -> Optional[bool]:
    assert hasattr(test, "transition_system")
    assert callable(test.transition_system)
    assert isinstance(env, PysmtEnv)
    _LOG_LVL = 0
    symbs, init, trans, fairness = test.transition_system(env)
    assert isinstance(symbs, frozenset)
    assert isinstance(init, FNode)
    assert isinstance(trans, FNode)
    assert isinstance(fairness, FNode)
    ts = TransSystem(env, symbs, [init], [trans])
    if hasattr(test, "hints"):
        assert callable(test.hints)
        hints = test.hints(env)
        assert isinstance(hints, frozenset)
        assert all(isinstance(h, Hint) for h in hints)
        if get_check_hints():
            for h in hints:
                correct, msgs = h.is_correct()
                if correct is not True:
                    log("\n".join(msgs), 0)
                if correct is False:
                    return False
    else:
        hints = frozenset([])

    return search_nonterm(ts, fairness,
                          hints, label, _LOG_LVL, out_dir)


def search_nonterm(ts: TransSystem, fairness: FNode,
                   hints: FrozenSet[Hint],
                   label: str, _LOG_LVL: int,
                   out_dir: Optional[str],
                   orig_trans: Optional[FNode] = None,
                   orig_ltl: Optional[str] = None) -> Optional[bool]:
    assert isinstance(ts, TransSystem)
    assert isinstance(ts.env, PysmtEnv)
    assert isinstance(fairness, FNode)
    assert isinstance(hints, frozenset)
    assert all(isinstance(h, Hint) for h in hints)
    assert isinstance(label, str)
    assert isinstance(_LOG_LVL, int)
    serialize = ts.env.serializer.serialize
    log(f"\tsymbols: {'; '.join(serialize(s) for s in ts.symbs)}")
    log(f"\tinit: {' & '.join(serialize(p) for p in ts.init)}", _LOG_LVL+1)
    log(f"\ttrans: {' & '.join(serialize(tr) for tr in ts.trans)}", _LOG_LVL+1)
    log(f"\tfairness: {serialize(fairness)}", _LOG_LVL+1)
    log(f"\thints: {', '.join(str(h) for h in hints)}\n", _LOG_LVL+1)
    floop = search_floop(ts, fairness, hints)
    if floop:
        assert isinstance(floop, FLoop)
        log(f"\n\tFound funnel-loop:\n {floop}", _LOG_LVL)
        if out_dir:
            assert False, "not implemented in newer version."
            out_f = path_join(out_dir, f"{label}.smv")
            with open(out_f, 'w', enc="utf-8") as out:
                floop.to_smv(ts, orig_trans, fairness, out,
                             orig_ltl=orig_ltl)
        return True
    log("\n\tFailed to synth non-termination argument\n", _LOG_LVL)
    return None


def set_options(opts):
    # approx
    approx_set_val_bound(opts.approx_max_val)
    set_approx_precision(opts.approx_precision)

    # BMC
    BMC.set_timeout(opts.bmc_timeout)
    BMC.set_max_k(opts.bmc_length)
    BMC.set_fair_lback(bool(opts.fair_lback))
    BMC.set_hints_mode(HintMode(opts.hint_mode))

    # EF-solver
    efsolver_timeout(opts.efsolver_timeout)
    efsolver_max_loops(opts.efsolver_iterations)
    set_ef_approximate(bool(opts.ef_approx_model))

    # motzkin
    motzkin_set_timeout(opts.motzkin_timeout)
    set_motzkin_approximate(bool(opts.motzkin_approx_model))

    # floop
    FLoopGen.set_min_loop_reps(opts.min_loop_repetitions)
    FLoop.set_min_ineqs(opts.min_inequalities)
    FLoop.set_max_ineqs(opts.max_inequalities)
    FLoop.set_propagate_max_it(opts.propagate_max_iterations)
    FLoop.set_preinst_inner_rf(bool(opts.preinst_inner_rf))
    Funnel.set_propagate_timeout(opts.propagate_timeout)
    Funnel.set_use_ef(bool(opts.use_ef))
    Funnel.set_use_motzkin(bool(opts.use_motzkin))

    # implicant
    Implicant.set_use_bool_impl(bool(opts.use_bool_impl))
    Implicant.set_use_unsat_cores(bool(opts.use_unsat_cores))
    Implicant.set_use_itp_impl(bool(opts.use_itp_impl))
    Implicant.set_minimize_core(bool(opts.minimize_core))
    Implicant.set_merge_ineqs(bool(opts.merge_ineqs))

    # other
    set_verbosity(opts.verbose)
    # set_use_generalised_lasso(bool(opts.generalised_lasso))
    set_div_mode(bool(opts.deterministic_diverging_monitor))
    set_solvers(opts.solvers)
    set_solver_name(opts.solvers[0])
    set_check_hints(bool(opts.check_hints))


def load_problem(test_file):
    test_spec = spec_from_file_location("test", test_file)
    test_module = module_from_spec(test_spec)
    test_spec.loader.exec_module(test_module)
    return test_module


def solve_problem(problem, label: str,
                  out_dir: Optional[str]) -> Optional[bool]:
    assert isinstance(label, str)
    assert not (hasattr(problem, "transition_system") and
                hasattr(problem, "check_ltl"))
    env = PysmtEnv()
    if hasattr(problem, "transition_system"):
        return run_test(problem, env, label, out_dir)
    assert hasattr(problem, "check_ltl")
    return run_ltl_test(problem, env, label, out_dir)


def run_f3(benchmark: str, out_dir: Optional[str]) -> None:
    assert benchmark.endswith(".py")
    label = path_basename(benchmark)[:-3]
    log(f"F3 run `{label}`", 0)
    start = time.time()
    prob = load_problem(benchmark)
    res = solve_problem(prob, label, out_dir)
    log(f"end of `{label}`: "
        f"{'SUCCESS' if res is True else 'FAILURE' if res is False else 'UNKNOWN'}"
        f" in {time.time() - start}s", 0)


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
    bmc.add_argument('-bmc-to', '--bmc-timeout', type=int,
                     default=BMC.get_timeout(),
                     help="set timeout for each BMC SMT query. "
                     f"({BMC.get_timeout()}s)")
    bmc.add_argument('-bmc-k', '--bmc-length', type=int,
                     default=BMC.get_max_k(),
                     help="set max BMC unrolling, 0 or negative for unbounded. "
                     f"({BMC.get_max_k()})")
    bmc.add_argument('-f-lback', '--fair-lback', type=int,
                     default=int(BMC.get_fair_lback()),
                     choices=[0, 1],
                     help="restrict candidate loops to the one in which "
                     f"loop-back state is fair. ({int(BMC.get_fair_lback())})")
    bmc.add_argument('-h-mode', '--hint-mode', type=int,
                     default=int(BMC.get_hints_mode()),
                     choices=list(map(int, HintMode)),
                     help="type of hint choice encoding; "
                     "0: may enable; 1: must enable at least 1; "
                     "2: must enable all. "
                     f"({int(BMC.get_hints_mode())})")

    ef = p.add_argument_group("Exists-Forall solver")
    ef.add_argument('-ef-to', '--efsolver-timeout', type=int,
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

    motzkin = p.add_argument_group("Exists-Forall solver via Motzkin-transposition")
    motzkin.add_argument('-motzkin-to', '--motzkin-timeout', type=int,
                         default=motzkin_get_timeout(),
                         help="set timeout for each SMT query generated via "
                         "Motzkin-transpose. "
                         f"({motzkin_get_timeout()}s)")
    motzkin.add_argument('-motzkin-approx', '--motzkin-approx-model', type=int,
                         default=int(get_motzkin_approximate()),
                         choices=[0, 1],
                         help="try simplify constants in Motzkin models. "
                         f"({int(get_motzkin_approximate())})")

    fnl = p.add_argument_group("Funnel")
    fnl.add_argument("-min-loop-reps", "--min-loop-repetitions", type=int,
                     default=FLoopGen.get_min_loop_reps(),
                     help="match only loops repeating at least the given "
                     f"number of times. ({FLoopGen.get_min_loop_reps()})")
    fnl.add_argument('-min-ineqs', '--min-inequalities', type=int,
                     default=FLoop.get_min_ineqs(),
                     help="set minimum number of extra inequalities in FLoop. "
                     f"({FLoop.get_min_ineqs()})")
    fnl.add_argument('-max-ineqs', '--max-inequalities', type=int,
                     default=FLoop.get_max_ineqs(),
                     help="set max number of extra inequalities in FLoop. "
                     f"({FLoop.get_max_ineqs()})")
    fnl.add_argument('-propagate-max-it', '--propagate-max-iterations',
                     type=int,
                     default=int(FLoop.get_propagate_max_it()),
                     help="max number of predicates backward propagations. "
                     f"({FLoop.get_propagate_max_it()})")
    fnl.add_argument('-preinst-rf', '--preinst-inner-rf',
                     type=int,  choices=[0, 1],
                     default=int(FLoop.get_preinst_inner_rf()),
                     help="try instantiate ranking functions for inner loops "
                     "before the search for an underapproximation. "
                     f"({int(FLoop.get_preinst_inner_rf())})")
    fnl.add_argument('-propagate-to', '--propagate-timeout', type=int,
                     default=int(Funnel.get_propagate_timeout()),
                     help="set timeout for inductiveness SMT-query for "
                     "predicates backward-propagation in inner loops. "
                     f"({Funnel.get_propagate_timeout()})s")
    fnl.add_argument('-ef', '--use-ef', type=int,
                     default=int(Funnel.get_use_ef()),
                     choices=[0, 1],
                     help="use EF-solver for EF quantified queries. "
                     f"({int(Funnel.get_use_ef())})")
    fnl.add_argument('-motzkin', '--use-motzkin', type=int,
                     default=int(Funnel.get_use_motzkin()),
                     choices=[0, 1],
                     help="use motzkin transposition to solve EF quantified "
                     f"queries. ({int(Funnel.get_use_motzkin())})")

    impl = p.add_argument_group("Implicant")
    impl.add_argument('-bool-impl', '--use-bool-impl', type=int,
                      default=int(Implicant.get_use_bool_impl()),
                      choices=[0, 1],
                      help="compute model-based boolean implicant. "
                      f"({int(Implicant.get_use_bool_impl())})")
    impl.add_argument('-itp-impl', '--use-itp-impl', type=int,
                      default=int(Implicant.get_use_itp_impl()),
                      choices=[0, 1],
                      help="use interpolants to compute implicant. "
                      f"({int(Implicant.get_use_itp_impl())})")
    impl.add_argument('-unsat-cores', '--use-unsat-cores', type=int,
                      default=int(Implicant.get_use_unsat_cores()),
                      choices=[0, 1],
                      help="use unsat-cores to compute implicant. "
                      f"({int(Implicant.get_use_unsat_cores())})")
    impl.add_argument('-min-core', '--minimize-core', type=int,
                      default=int(Implicant.get_minimize_core()),
                      choices=[0, 1],
                      help="shrink unsat-core to obtain a minimal one w.r.t inequalities. "
                      f"({int(Implicant.get_minimize_core())})")
    impl.add_argument('-merge-ineqs', '--merge-ineqs', type=int,
                      default=int(Implicant.get_merge_ineqs()),
                      choices=[0, 1],
                      help="merge a <= b & b >= a into a = b in implicants. "
                      f"({int(Implicant.get_merge_ineqs())})")

    other = p.add_argument_group("Other")
    other.add_argument('-v', '--verbose', type=int, default=get_verbosity(),
                       help=f"set verbosity level. ({get_verbosity()})")
    other.add_argument('-s', '--solvers', type=str, nargs='+',
                       default=["msat", "z3"],
                       help="set list of available solvers, "
                       "see `pysmt-install --check`.")
    # other.add_argument('-generalised-lasso', '--generalised-lasso', type=int,
    #                    default=int(get_use_generalised_lasso()),
    #                    choices=[0, 1],
    #                    help="enable/disable detection of generalised lasso using "
    #                    "pattern described in Timed-nuXmv paper CAV 2019. "
    #                    f"({int(get_use_generalised_lasso())})")
    other.add_argument('-det-div', '--deterministic-diverging-monitor',
                       type=int,
                       default=int(get_div_mode()),
                       choices=[0, 1],
                       help="1: use deterministic diverging monitor, "
                       "0: use nondeterministic reset for diverging monitor. "
                       f"({int(get_div_mode())})")
    other.add_argument('-smv-out', '--smv-out', type=str, default=None,
                       help="write smv representation of nontermination "
                       "argument in the given directory.")
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
    set_options(opts)
    run_f3(opts.benchmark, opts.smv_out)


if __name__ == "__main__":
    main(config_args().parse_args())
