#! /usr/bin/env python3
# -*- coding: utf-8 -*-

import os
import re
import argparse
from subprocess import check_output, CalledProcessError, STDOUT, TimeoutExpired

NUXMV_TIMEOUT = 250

CMD_CHECK_INVARSPEC = """set on_failure_script_quits 1
go_msat
check_invar_ic3 -P {}
quit
"""

CMD_CHECK_LTLSPEC = """set on_failure_script_quits 1
go_msat
check_ltlspec_ic3 -P {}
quit
"""

CMD_CHECK_NOT_EMPTY = CMD_CHECK_INVARSPEC.format("NOT_EMPTY")

CMD_CHECK_UNDERAPPROX = CMD_CHECK_INVARSPEC.format("UNDERAPPROX")

CMD_CHECK_FAIR = CMD_CHECK_LTLSPEC.format("GF_FAIR")


MATCH_TRUE_INVARSPEC = re.compile(r"invariant\s+.*\s+is true")
MATCH_FALSE_INVARSPEC = re.compile(r"invariant\s+.*\s+is false")
MATCH_TRUE_LTLSPEC = re.compile(r"LTL specification\s+.*\s+is true")
MATCH_FALSE_LTLSPEC = re.compile(r"LTL specification\s+.*\s+is false")


def collect_spec_names(smv_model_f: str, skip=None,
                       spec_type="INVARSPEC") -> list:
    assert os.path.isfile(smv_model_f)
    assert skip is None or isinstance(skip, (list, set, frozenset))
    skip = frozenset(skip) if skip else frozenset()
    res = []
    regexp = re.compile(r"{}\s+NAME\s*(?P<name>\S*)\s*:="
                        .format(spec_type))
    with open(smv_model_f, 'r') as in_f:
        for line in in_f:
            match = regexp.search(line)
            if match:
                name = match.group("name").strip()
                if name not in skip:
                    res.append(name)
    return res


def run_nuxmv(exe: str, model_file: str, cmd_file: str):
    """Run nuXmv executable `exe` on the given model with the commands
    `exe_cmd`"""
    assert os.path.isfile(exe), "Not a file: {}".format(exe)
    assert os.path.isfile(model_file), "Not a file: {}".format(model_file)
    assert os.path.isfile(cmd_file), "Not a file: {}".format(cmd_file)

    cmd = [exe, "-source", cmd_file, model_file]
    try:
        res = check_output(cmd, stderr=STDOUT, timeout=NUXMV_TIMEOUT,
                           universal_newlines=True)
    except (CalledProcessError, TimeoutError, TimeoutExpired):
        res = None
    # res = subprocess.run(cmd,
    #                      stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    return res


def main(opts):
    global NUXMV_TIMEOUT
    NUXMV_TIMEOUT = opts.nuxmv_timeout
    nuxmv = opts.nuxmv
    if not os.path.isfile(nuxmv):
        print("Not a file: {}".format(nuxmv))
        return

    nuxmv_cmd_dir = opts.nuxmv_cmd
    if not os.path.isdir(nuxmv_cmd_dir):
        print("Not a directory: {}".format(nuxmv_cmd_dir))
        return

    bench_files = set()
    for _curr_path in opts.benchmarks:
        curr_path = os.path.abspath(_curr_path)
        if os.path.isfile(curr_path):
            assert curr_path.endswith(".smv")
            bench_files.add((os.path.basename(_curr_path)[:-4], curr_path))
        elif os.path.isdir(curr_path):
            curr_paths = [curr_path]
            while curr_paths:
                curr_path = curr_paths.pop()
                for _f_name in os.listdir(curr_path):
                    f_name = os.path.join(curr_path, _f_name)
                    if os.path.isfile(f_name) and \
                       _f_name.endswith(".smv") and \
                       not _f_name.startswith("_"):
                        bench_files.add((_f_name[:-4], f_name))
                    elif os.path.isdir(f_name) and not f_name.endswith("__"):
                        curr_paths.append(f_name)

    # cmd_files = [os.path.join(nuxmv_cmd_dir, "not_empty.cmd"),
    #              os.path.join(nuxmv_cmd_dir, "underapprox.cmd"),
    #              os.path.join(nuxmv_cmd_dir, "gf_fair.cmd")]
    # expected_res = [re.compile(r"invariant .* is false"),
    #                 re.compile(r"invariant .* is true"),
    #                 re.compile(r"LTL specification .* is true")]
    # cmds = [CMD_CHECK_NOT_EMPTY,
    #         CMD_CHECK_UNDERAPPROX,
    #         CMD_CHECK_FAIR]
    # for f, cmd in zip(cmd_files, cmds):
    #     with open(f, 'w') as out_f:
    #         out_f.write(cmd)
    bench_files = sorted(bench_files)
    num_tests = len(bench_files)
    failed_tests = []
    for test_num, (label, test_file) in enumerate(bench_files):
        assert os.path.isfile(test_file)
        print("\n\nrun {}/{}: `{}`".format(test_num + 1, num_tests, label))
        false_invar_names = ["NOT_EMPTY"]
        true_invar_names = collect_spec_names(test_file,
                                              skip=false_invar_names)
        false_ltl_names = []
        true_ltl_names = collect_spec_names(test_file,
                                            skip=false_ltl_names,
                                            spec_type="LTLSPEC")
        cmd_file = os.path.join(nuxmv_cmd_dir, "check_invar.cmd")
        errors = []
        # check false INVARSPEC
        res_re = MATCH_FALSE_INVARSPEC
        for invar_name in false_invar_names:
            with open(cmd_file, 'w') as out_f:
                out_f.write(CMD_CHECK_INVARSPEC.format(invar_name))
            print("\tCheck {}".format(invar_name))
            nuxmv_res = run_nuxmv(nuxmv, test_file, cmd_file)
            if nuxmv_res is None:
                errors.append("nuXmv timeout in `{}`".format(invar_name))
            else:
                if res_re.search(nuxmv_res) is None:
                    errors.append(invar_name)
        # check true INVARSPEC
        res_re = MATCH_TRUE_INVARSPEC
        for invar_name in true_invar_names:
            with open(cmd_file, 'w') as out_f:
                out_f.write(CMD_CHECK_INVARSPEC.format(invar_name))
            print("\tCheck {}".format(invar_name))
            nuxmv_res = run_nuxmv(nuxmv, test_file, cmd_file)
            if nuxmv_res is None:
                errors.append("nuXmv timeout in `{}`".format(invar_name))
            else:
                if res_re.search(nuxmv_res) is None:
                    errors.append(invar_name)

        # check false LTLSPEC
        res_re = MATCH_FALSE_LTLSPEC
        for invar_name in false_ltl_names:
            with open(cmd_file, 'w') as out_f:
                out_f.write(CMD_CHECK_LTLSPEC.format(invar_name))
            print("\tCheck {}".format(invar_name))
            nuxmv_res = run_nuxmv(nuxmv, test_file, cmd_file)
            if nuxmv_res is None:
                errors.append("nuXmv timeout in `{}`".format(invar_name))
            else:
                if res_re.search(nuxmv_res) is None:
                    errors.append(invar_name)
        # check true LTLSPEC
        res_re = MATCH_TRUE_LTLSPEC
        for invar_name in true_ltl_names:
            with open(cmd_file, 'w') as out_f:
                out_f.write(CMD_CHECK_LTLSPEC.format(invar_name))
            print("\tCheck {}".format(invar_name))
            nuxmv_res = run_nuxmv(nuxmv, test_file, cmd_file)
            if nuxmv_res is None:
                errors.append("nuXmv timeout in `{}`".format(invar_name))
            else:
                if res_re.search(nuxmv_res) is None:
                    errors.append(invar_name)

        if errors:
            print("FAILURE: {} did not satisfy or unknown:\n\t{}"
                  .format(label, "\n\t".join(errors)))
            failed_tests.append(label)
        else:
            print("SUCCESS: {} passed all checks".format(label))
    if failed_tests:
        print("\nFound errors or unknowns in: {}"
              .format(", ".join(failed_tests)))
    else:
        print("\nAll tests were successful")


def getopts():
    p = argparse.ArgumentParser()
    p.add_argument('-nuxmv', '--nuxmv', type=str,
                   help="path to nuXmv binary")
    p.add_argument('-nuxmv-t', '--nuxmv-timeout', type=int,
                   default=NUXMV_TIMEOUT,
                   help="set timeout for each NUXMV run ({}s)"
                   .format(NUXMV_TIMEOUT))
    p.add_argument('-nuxmv-cmd', '--nuxmv-cmd', type=str,
                   default="/tmp",
                   help="directory where to write the nuXmv cmd files")
    p.add_argument("benchmarks", nargs="+",
                   help="list of smv files or directories containing them")
    return p.parse_args()


if __name__ == "__main__":
    main(getopts())
