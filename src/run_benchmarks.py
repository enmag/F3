#! /usr/bin/env python3
# -*- coding: utf-8 -*-
import os
from run_f3 import config_args, set_options, run_f3
from utils import log

if __debug__:
    import faulthandler
    faulthandler.enable()


def main(opts):
    # make sure methods in Pysmt do not use global environment.
    from pysmt.environment import pop_env
    pop_env()
    if __debug__:
        from pysmt.environment import ENVIRONMENTS_STACK
        assert len(ENVIRONMENTS_STACK) == 0

    out_dir = opts.smv_out
    set_options(opts)

    bench_files = set()
    benchmarks = list(opts.benchmarks)
    benchmarks.append(opts.benchmark)
    while benchmarks:
        _curr_path = benchmarks.pop()
        curr_path = os.path.abspath(_curr_path)
        assert os.path.isfile(curr_path) or os.path.isdir(curr_path)
        if os.path.isfile(curr_path) and curr_path.endswith(".py"):
            bench_files.add((os.path.basename(_curr_path)[:-3], curr_path))
        elif os.path.isdir(curr_path):
            benchmarks.extend(os.path.join(curr_path, f_name)
                              for f_name in os.listdir(curr_path))

    num_tests = len(bench_files)
    for test_num, (_, test_file) in enumerate(sorted(bench_files)):
        assert os.path.isfile(test_file)
        # execute test function.
        log(f"\n\nProblem {test_num + 1} of {num_tests}: {test_file}", 0)
        run_f3(test_file, out_dir)


if __name__ == "__main__":
    argp = config_args()
    argp.add_argument("benchmarks", nargs='*', type=str,
                      help="python file or directory containing "
                      "the problems to be solved.")
    main(argp.parse_args())
