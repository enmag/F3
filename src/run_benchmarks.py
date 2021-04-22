#! /usr/bin/env python3
# -*- coding: utf-8 -*-
from typing import Optional
import os
import time
import argparse
from importlib.util import spec_from_file_location, module_from_spec
from collections.abc import Iterable
from itertools import chain

from pysmt.environment import get_env, reset_env
from pysmt.fnode import FNode

from ltl.ltl import LTLEncoder, Options

from unranker import search_unrank_bmc
from solver import Solver
from smv_printer import ltl_to_smv
from encode_diverging import encode_diverging
from utils import log, symb_to_next, symb_is_next


if __debug__:
    import faulthandler
    faulthandler.enable()


def run_ltl_test(test, label: Optional[str] = None, out_dir=None):
    assert hasattr(test, "check_ltl")
    assert callable(test.check_ltl)
    env = get_env()
    reset_env()
    mgr = env.formula_manager
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
        div_symbs: frozenset = frozenset()
        if hasattr(test, "diverging_symbs"):
            assert callable(test.diverging_symbs)
            div_symbs = test.diverging_symbs(menv)
        assert all(div_s in msat_symbs.keys() for div_s in div_symbs)
        for div_s in div_symbs:
            msat_symbs, msat_init, msat_trans, msat_ltl = \
                encode_diverging(menv, enc, div_s,
                                 msat_symbs, msat_init,
                                 msat_trans, msat_ltl)
        ts = enc.encode(msat_symbs, msat_ltl)
        div_symbs = frozenset(convert(s) for s in div_symbs)
        assert all(symb_to_next(mgr, convert(s)) == convert(x_s)
                   for s, x_s in msat_symbs.items())

        symbols = [convert(s) for s in msat_symbs.keys()] + \
                  [convert(s[1]) for s in enc.fairness_vars()]
        ltl_str = ltl_to_smv(env, solver, enc, msat_ltl) if out_dir else None
        orig_trans = convert(msat_trans)
        init = mgr.And(convert(msat_init), convert(ts.init()))
        trans = mgr.And(orig_trans, convert(ts.trans()))
        fairness = mgr.Not(convert(ts.prop()))
    symbols.extend([s for s in
                    chain.from_iterable([init.get_free_variables(),
                                         trans.get_free_variables(),
                                         fairness.get_free_variables()])
                    if s.symbol_name().startswith("_EL_")])
    symbols = frozenset(symbols)

    assert all(not symb_is_next(s) for s in symbols)
    assert init.get_free_variables() <= symbols | \
        frozenset(symb_to_next(mgr, s) for s in symbols)
    assert fairness.get_free_variables() <= symbols
    assert trans.get_free_variables() <= symbols | \
        frozenset(symb_to_next(mgr, s) for s in symbols)
    assert ts.live_prop()

    hints = None
    if hasattr(test, "hints"):
        assert callable(test.hints)
        hints = test.hints()
        assert isinstance(hints, Iterable)
        assert False, "TODO implement hints handling"
    return search_nonterm(env, symbols, init, trans, fairness,
                          label, _LOG_LVL, out_dir,
                          orig_trans=orig_trans,
                          orig_ltl=ltl_str)


def run_test(test, label: Optional[str] = None, out_dir=None):
    assert hasattr(test, "transition_system")
    assert callable(test.transition_system)
    env = get_env()
    reset_env()
    _LOG_LVL = 0
    symbols, init, trans, fairness = test.transition_system(env)
    assert isinstance(symbols, frozenset)
    assert isinstance(init, FNode)
    assert isinstance(trans, FNode)
    assert isinstance(fairness, FNode)
    hints = None
    if hasattr(test, "hints"):
        assert callable(test.hints)
        hints = test.hints()
        assert isinstance(hints, Iterable)
        assert False, "TODO implement hints handling"
    return search_nonterm(env, symbols, init, trans, fairness,
                          label, _LOG_LVL, out_dir)


def search_nonterm(env, symbols: frozenset,
                   init: FNode, trans: FNode, fairness: FNode,
                   label: Optional[str],
                   _LOG_LVL: int, out_dir=None, orig_trans=None,
                   orig_ltl: Optional[str] = None):
    assert isinstance(symbols, frozenset)
    assert isinstance(init, FNode)
    assert isinstance(trans, FNode)
    assert isinstance(fairness, FNode)
    assert label is None or isinstance(label, str)
    assert isinstance(_LOG_LVL, int)
    log("\tinit: {}".format(init.serialize()), _LOG_LVL+1)
    log("\ttrans: {}".format(trans.serialize()), _LOG_LVL+1)
    log("\tfairness: {}".format(fairness.serialize()), _LOG_LVL+1)
    # log("\thints: {}\n".format(hints), _LOG_LVL)
    start = time.time()
    _, arg0, arg1 = search_unrank_bmc(env, symbols, init, trans,
                                      fairness)
    runtime = time.time() - start
    success = False
    if arg0 is not None:
        if isinstance(arg0, frozenset):
            assert isinstance(arg1, frozenset)
            log("\n\tFound non-termination argument based on generalised lasso:\n"
                "\tpos diverging vars: {};\n\tneg diverging vars: {};"
                .format(arg0, arg1),
                _LOG_LVL)
        else:
            nonterm = "\t{}".format(arg0) if arg1 is None \
                      else arg0.describe(arg1, indent="\t")
            log("\n\tFound non-termination argument:\n{}".format(nonterm),
                _LOG_LVL)
        success = True
    else:
        log("\n\tFailed to synth non-termination argument\n", _LOG_LVL)
    if out_dir and arg1 is not None:
        out_f = os.path.join(out_dir, "{}.smv".format(label))
        with open(out_f, "w") as out:
            if orig_trans is None:
                orig_trans = trans
            arg.to_smv(orig_trans, fairness, arg1, out,
                       orig_ltl=orig_ltl)
    reset_env()
    return success, runtime


def dispatch_test(test, label: Optional[str] = None, out_dir=None):
    assert label is None or isinstance(label, str)
    assert not (hasattr(test, "transition_system") and
                hasattr(test, "check_ltl"))
    if hasattr(test, "transition_system"):
        return run_test(test, label, out_dir)
    assert hasattr(test, "check_ltl")
    return run_ltl_test(test, label, out_dir)


def main(opts):
    set_verbosity(opts.verbose)

    set_use_ef_rf(bool(opts.use_ef_rf))
    set_rf_timeout(opts.synth_rf_motzkin_timeout)
    set_use_motzkin_rf(bool(opts.use_motzkin_rf))
    set_use_motzkin(bool(opts.use_motzkin))
    set_learn_ef(bool(opts.motzkin_learn_ef))
    NonterminationArg.set_timeout(opts.motzkin_timeout)
    NonterminationArg.set_min_ineqs(opts.min_inequalities)
    NonterminationArg.set_max_ineqs(opts.max_inequalities)
    NonterminationArg.set_constr_propagate(opts.constr_propagate)
    # set_nonterm_factory(opts.nonterm_factory)

    BMC.set_timeout(opts.bmc_timeout)
    BMC.set_max_k(opts.bmc_length)
    BMC.set_loop_ext_factor(opts.loop_extension_bound)
    Generaliser.set_use_bool_impl(bool(opts.use_bool_impl))
    Generaliser.set_use_unsat_cores(bool(opts.use_unsat_cores))
    Generaliser.set_merge_ineqs(bool(opts.merge_ineqs))

    set_use_ef(bool(opts.use_ef))
    efsolver_timeout(opts.efsolver_timeout)
    efsolver_max_loops(opts.efsolver_iterations)

    set_use_generalised_lasso(bool(opts.generalised_lasso))
    approx_set_val_bound(opts.approx_max_val)
    set_approx_precision(opts.approx_precision)

    set_solvers(opts.solvers)
    set_solver_name(opts.solvers[0])

    out_dir = opts.smv_out

    bench_files = set()
    for _curr_path in opts.benchmarks:
        curr_path = os.path.abspath(_curr_path)
        if os.path.isfile(curr_path):
            assert curr_path.endswith(".py")
            bench_files.add((os.path.basename(_curr_path)[:-3], curr_path))
        elif os.path.isdir(curr_path):
            curr_paths = [curr_path]
            while curr_paths:
                curr_path = curr_paths.pop()
                for _f_name in os.listdir(curr_path):
                    f_name = os.path.join(curr_path, _f_name)
                    if os.path.isfile(f_name) and _f_name.endswith(".py") and \
                       not _f_name.startswith("_"):
                        bench_files.add((_f_name[:-3], f_name))
                    elif os.path.isdir(f_name) and not f_name.endswith("__"):
                        curr_paths.append(f_name)

        else:
            assert False, "{} does not exist".format(curr_path)
    bench_files = sorted(bench_files)
    num_tests = len(bench_files)
    for test_num, (label, test_file) in enumerate(bench_files):
        assert os.path.isfile(test_file)
        # load test file.
        test_spec = spec_from_file_location("test", test_file)
        test_module = module_from_spec(test_spec)
        test_spec.loader.exec_module(test_module)

        # execute test function.
        print("\n\nrun {}/{}: `{}`".format(test_num + 1, num_tests, label))
        res, runtime = dispatch_test(test_module, label, out_dir)
        if res is True:
            result_str = "SUCCESS in {}s".format(runtime)
        elif res is False:
            result_str = "FAILURE in {}s".format(runtime)
        else:
            result_str = "UNKNOWN in {}s".format(runtime)
        print("end of `{}`: {}".format(label, result_str))


def getopts():
    p = argparse.ArgumentParser()
    p.add_argument('-v', '--verbose', type=int, default=get_verbosity(),
                   help="set verbosity level ({})".format(get_verbosity()))

    p.add_argument('-rf-motzkin-t', '--synth-rf-motzkin-timeout', type=int,
                   default=get_rf_timeout(),
                   help="set timeout for Motzkin SMT queries for RF synthesis"
                   "({}s)".format(get_rf_timeout()))
    p.add_argument('-motzkin', '--use-motzkin', type=int,
                   default=int(get_use_motzkin()),
                   help="use motzkin transposition to solve EF quantified "
                   "queries ({})".format(int(get_use_motzkin())))
    p.add_argument('-motzkin-rf', '--use-motzkin-rf', type=int,
                   default=int(get_use_motzkin_rf()),
                   help="use motzkin transposition to solve EF quantified "
                   "queries for ranking function ({})"
                   .format(int(get_use_motzkin_rf())))
    p.add_argument('-motzkin-t', '--motzkin-timeout', type=int,
                   default=NonterminationArg.get_timeout(),
                   help="set timeout for each Motzkin-generated "
                   "SMT query ({}s)"
                   .format(NonterminationArg.get_timeout()))
    p.add_argument('-learn-ef', '--motzkin-learn-ef', type=int,
                   default=int(get_learn_ef()),
                   help="add constraints learned by EF-solver to "
                   "motzkin SMT-query ({})".format(int(get_learn_ef())))

    p.add_argument('-ef', '--use-ef', type=int, default=int(get_use_ef()),
                   help="use EF-solver for EF quantified queries "
                   "({})".format(int(get_use_ef())))
    p.add_argument('-ef-rf', '--use-ef-rf', type=int,
                   default=int(get_use_ef_rf()),
                   help="use EF-solver for EF quantified queries for "
                   "Ranking Funciton ({})".format(int(get_use_ef_rf())))
    p.add_argument('-ef-t', '--efsolver-timeout', type=int,
                   default=efsolver_get_timeout(),
                   help="set timeout for each SMT query in EF-solver ({}s)"
                   .format(efsolver_get_timeout()))
    p.add_argument('-ef-its', '--efsolver-iterations', type=int,
                   default=efsolver_get_max_loops(),
                   help="set max number of iteration in EF-solver ({})"
                   .format(efsolver_get_max_loops()))
    p.add_argument('-approx-prec', '--approx-precision', type=int,
                   default=get_approx_precision(),
                   help="precision of approximation of rational values "
                   "to simplify constants in models; -1 to disable ({})"
                   .format(get_approx_precision()))
    p.add_argument('-approx-max-val', '--approx-max-val', type=int,
                   default=approx_get_val_bound(),
                   help="try to keep constants below provided number ({})"
                   .format(approx_get_val_bound()))

    p.add_argument('-bmc-t', '--bmc-timeout', type=int,
                   default=BMC.get_timeout(),
                   help="set timeout for each BMC SMT query ({}s)"
                   .format(BMC.get_timeout()))
    p.add_argument('-bmc-k', '--bmc-length', type=int, default=BMC.get_max_k(),
                   help="set max BMC unrolling, 0 or negative for unbounded "
                   "({})".format(BMC.get_max_k()))
    p.add_argument('-max-extend', '--loop_extension_bound', type=int,
                   default=BMC.get_loop_ext_factor(),
                   help="consider only abstract loops for which there exists "
                   "an extension with length <= "
                   "loop_extension_bound * len(loop) "
                   "({})".format(BMC.get_loop_ext_factor()))
    p.add_argument('-bool-impl', '--use-bool-impl', type=int,
                   default=int(Generaliser.get_use_bool_impl()),
                   help="compute model-based boolean implicant to generalise "
                   "path ({})".format(int(Generaliser.get_use_bool_impl())))
    p.add_argument('-unsat-cores', '--use-unsat-cores', type=int,
                   default=int(Generaliser.get_use_unsat_cores()),
                   help="use unsat-cores to generalise path ({})"
                   .format(int(Generaliser.get_use_unsat_cores())))
    p.add_argument('-merge-ineqs', '--merge-ineqs', type=int,
                   default=int(Generaliser.get_merge_ineqs()),
                   help="merge a <= b & b >= a into a = b "
                   "during path generalisation ({})"
                   .format(int(Generaliser.get_merge_ineqs())))

    p.add_argument('-s', '--solvers', type=str, nargs='+',
                   default=["msat", "z3"],
                   help="set list of available solvers, "
                   "see `pysmt-install --check`")
    p.add_argument('-min-ineqs', '--min-inequalities', type=int,
                   default=NonterminationArg.get_min_ineqs(),
                   help="set minimum number of inequalities in nontermination "
                   "argument ({})".format(NonterminationArg.get_min_ineqs()))
    p.add_argument('-max-ineqs', '--max-inequalities', type=int,
                   default=NonterminationArg.get_max_ineqs(),
                   help="set max number of inequalities in nontermination "
                   "argument ({})".format(NonterminationArg.get_max_ineqs()))

    p.add_argument('-propagate', '--constr-propagate', type=int,
                   default=int(NonterminationArg.get_constr_propagate()),
                   choices=[0, 1, 2],
                   help="backward propagate constraints in Funnels "
                   "0: no; 1: partial; 2: full;"
                   "({})".format(NonterminationArg.get_constr_propagate()))
    # p.add_argument('-nonterm-f', '--nonterm-factory', type=str,
    #                choices=['cartesian', 'sat'],
    #                default=get_nonterm_factory_str(),
    #                help="set nontermination argument template factory "
    #                "({})".format(get_nonterm_factory_str()))

    p.add_argument('-generalised-lasso', '--generalised-lasso', type=int,
                   default=int(get_use_generalised_lasso()),
                   choices=[0, 1],
                   help="enable/disable detection of generalised lasso using "
                   "pattern described in Timed-nuXmv paper CAV 2019;"
                   "({})".format(int(get_use_generalised_lasso())))

    p.add_argument('-smv-out', '--smv-out', type=str, default=None,
                   help="write smv representation of nontermination argument"
                   "in the given directory")

    p.add_argument("benchmarks", nargs="+",
                   help="list of files or directories containing benchmarks")
    return p.parse_args()


if __name__ == "__main__":
    from utils import set_verbosity, get_verbosity
    from abstract_loops import BMC
    from efsolver import set_timeout as efsolver_timeout
    from efsolver import get_timeout as efsolver_get_timeout
    from efsolver import set_maxloops as efsolver_max_loops
    from efsolver import get_maxloops as efsolver_get_max_loops
    from rationalapprox import get_approx_precision, set_approx_precision
    from rationalapprox import get_val_bound as approx_get_val_bound
    from rationalapprox import set_val_bound as approx_set_val_bound
    from solver import set_solvers, set_solver_name
    from unranker import set_use_ef, get_use_ef, \
        set_use_motzkin, get_use_motzkin, \
        set_use_ef_rf, get_use_ef_rf, \
        set_use_motzkin_rf, get_use_motzkin_rf, \
        set_learn_ef, get_learn_ef, \
        get_use_generalised_lasso, set_use_generalised_lasso, \
        set_nonterm_factory, get_nonterm_factory_str
    from funnel import NonterminationArg
    from ranker import set_rf_timeout, get_rf_timeout
    from generalise_path import Generaliser

    main(getopts())
