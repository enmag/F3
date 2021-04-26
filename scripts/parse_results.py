#! /usr/bin/env python3

import os
import re
import argparse
import sys
from glob import glob

TO = 3600

tool2ext = {
    "anant": "t2",
    "aprove": "c",
    "divine": "xml",
    "mitlbmc": "tsmv",
    "nuxmv": "smv",
    "f3": "py",
    "t2": "t2",
    "ultimate": "c",
    "uppaal": "xml"
}

known_errors = {}
known_errors["anant"] = frozenset([
    # Anant does not support division by integer.
    "ChenFlurMukhopadhyay-SAS2012-Ex2.05_false-termination",
    "Division_false-termination",
    # anant internally generates an expression with `%` that it does not handle.
    "BradleyMannaSipma-CAV2005-Fig1-modified_false-termination"
])
known_errors["aprove"] = frozenset([
    # crashing thread
    "15"
])
known_errors["divine"] = frozenset([])
known_errors["f3"] = frozenset([])
known_errors["t2"] = frozenset([])
known_errors["ultimate"] = frozenset([])


def get_exec_time(stats) -> float:
    assert os.path.isfile(stats)
    real_time_re = re.compile(r"real\s*:\s+(?P<num>\d+(\.\d+)?)")
    user_time_re = re.compile(r"user\s*:\s+(?P<num>\d+(\.\d+)?)")
    sys_time_re = re.compile(r"sys\s*:\s+(?P<num>\d+(\.\d+)?)")
    r_time = None
    u_time = None
    s_time = None
    with open(stats, 'r') as in_f:
        for line in in_f:
            line = line.strip()
            match = real_time_re.match(line)
            if match:
                assert "num" in match.groupdict()
                assert r_time is None
                r_time = float(match["num"])
            else:
                match = user_time_re.match(line)
                if match:
                    assert "num" in match.groupdict()
                    assert u_time is None
                    u_time = float(match["num"])
                else:
                    match = sys_time_re.match(line)
                    if match:
                        assert "num" in match.groupdict()
                        assert s_time is None
                        s_time = float(match["num"])
            if r_time is not None and u_time is not None and s_time is not None:
                break
    if r_time is None:
        raise Exception("Real time not found in {}".format(stats))
    if u_time is None:
        raise Exception("User time not found in {}".format(stats))
    if s_time is None:
        raise Exception("Sys time not found in {}".format(stats))
    return max(r_time, u_time + s_time)


def check_anant(stdout, stderr) -> str:
    assert os.path.isfile(stdout)
    assert os.path.isfile(stderr)
    assert stdout.endswith(".{}.stdout".format(tool2ext["anant"]))
    assert stderr.endswith(".{}.stderr".format(tool2ext["anant"]))
    label = os.path.basename(stdout)[:-len(".{}.stdout"
                                           .format(tool2ext["anant"]))]
    correct = re.compile(r"Result\s*:\s*Non-Terminating")
    wrong = re.compile(r"Result\s*:\s*Terminating")
    unknown = re.compile(r"Result\s*:\s*Unknown")
    error = re.compile(r"error", re.IGNORECASE)
    res = None
    with open(stdout, "r") as in_f:
        for line in in_f:
            line = line.strip()
            if correct.match(line):
                assert res is None
                res = "correct"
            elif wrong.match(line):
                assert res is None
                res = "error"
            elif unknown.match(line):
                assert res is None
                res = "unknown"
            if error.search(line):
                res = "unknown"
                if label not in known_errors["anant"]:
                    print("Found anant ERROR in {}".format(stdout))
                # sys.exit(0)
    return res if res else "timeout"


def check_aprove(stdout, stderr) -> str:
    assert os.path.isfile(stdout)
    assert os.path.isfile(stderr)
    assert stdout.endswith(".{}.stdout".format(tool2ext["aprove"]))
    assert stderr.endswith(".{}.stderr".format(tool2ext["aprove"]))
    label = os.path.basename(stdout)[:-len(".{}.stdout"
                                           .format(tool2ext["aprove"]))]
    correct = re.compile(r"NO")
    wrong = re.compile(r"YES")
    unknown = re.compile(r"MAYBE")
    memout = re.compile(r"(OutOfMemoryError)|(insufficient memory for the Java Runtime Environment to continue)", re.IGNORECASE)
    error = re.compile(r"(exception)|(TIMEOUT)", re.IGNORECASE)
    res = None
    with open(stdout, "r") as in_f:
        for line in in_f:
            line = line.strip()
            if correct.match(line):
                assert res is None
                res = "correct"
            elif wrong.match(line):
                assert res is None
                res = "error"
            elif unknown.match(line):
                assert res is None
                res = "unknown"
            elif memout.search(line):
                res = "memout"
            if error.search(line):
                res = "unknown"
                if label not in known_errors["aprove"]:
                    print("Found aprove ERROR in {}".format(stdout))
    if res is None:
        with open(stderr, "r") as in_f:
            for line in in_f:
                line = line.strip()
                if memout.search(line):
                    res = "memout"
                elif error.search(line):
                    res = "unknown"
                    if label not in known_errors["aprove"]:
                        print("Found aprove ERROR in {}".format(stderr))
                if res is not None:
                    break
    return res if res else "timeout"


def check_divine(stdout, stderr) -> str:
    assert os.path.isfile(stdout)
    assert os.path.isfile(stderr)
    assert stdout.endswith(".{}.stdout".format(tool2ext["divine"]))
    assert stderr.endswith(".{}.stderr".format(tool2ext["divine"]))
    label = os.path.basename(stdout)[:-len(".{}.stdout"
                                           .format(tool2ext["divine"]))]

    correct = re.compile(r"\s*The\s+property\s+DOES\s+NOT\s+hold")
    wrong = re.compile(r"\s*The\s+property\s+holds")
    memout = re.compile(r".*(Cannot\s+allocate\s+memory)|(std::bad_alloc)")
    unknown = re.compile(r"Segmentation fault", re.IGNORECASE)
    error = re.compile(r"(exception)|(TIMEOUT)|(\s+error)|(parse)", re.IGNORECASE)
    res = None
    with open(stderr, "r") as in_f:
        for line in in_f:
            line = line.strip()
            if correct.match(line):
                assert res is None
                res = "correct"
                break
            elif wrong.match(line):
                assert res is None
                res = "error"
                break
            elif memout.match(line):
                assert res is None or res in {"error", "memout"}
                res = "memout"
            elif unknown.search(line):
                res = "unknown"
            elif error.search(line) and res != "memout":
                if label not in known_errors["divine"]:
                    res = "error"
                else:
                    res = "unknown"
    if res == "error":
        print("Found DIVINE ERROR in {}".format(stderr))
        sys.exit(0)
    return res if res else "timeout"


def check_mitlbmc(stdout, stderr) -> str:
    assert os.path.isfile(stdout)
    assert os.path.isfile(stderr)
    assert stdout.endswith(".{}.stdout".format(tool2ext["mitlbmc"]))
    assert stderr.endswith(".{}.stderr".format(tool2ext["mitlbmc"]))
    label = os.path.basename(stdout)[:-len(".{}.stdout"
                                           .format(tool2ext["mitlbmc"]))]
    correct = re.compile(r"Property\s+\d+\s+.*does\s+not\s+hold")
    wrong = re.compile(r"Property\s+\d+\s+.*holds")
    error = re.compile(r"(\s+error\s+)|(exception)|(Exception)|(cannot open)|(must be built)",
                       re.IGNORECASE)
    res = None
    with open(stdout, "r") as in_f:
        for line in in_f:
            line = line.strip()
            if correct.match(line):
                assert res is None
                res = "correct"
            elif wrong.match(line):
                assert res is None
                res = "error"
            if error.search(line):
                res = "unknown"
                if label not in known_errors["divine"]:
                    print("Found mitlbmc ERROR in {}".format(stdout))
    return res if res else "timeout"


def check_nuxmv(stdout, stderr) -> str:
    assert os.path.isfile(stdout)
    assert os.path.isfile(stderr)
    assert stdout.endswith(".{}.stdout".format(tool2ext["nuxmv"]))
    assert stderr.endswith(".{}.stderr".format(tool2ext["nuxmv"]))
    label = os.path.basename(stdout)[:-len(".{}.stdout"
                                           .format(tool2ext["nuxmv"]))]
    correct = re.compile(r"-- (LTL )?specification\s+.*\s+is\s+false")
    wrong = re.compile(r"-- (LTL )?specification\s+.*\s+is\s+true")
    memout = re.compile(r"Out of memory", re.IGNORECASE)
    error = re.compile(r"(ERROR)|(cannot open)|(must be built)")
    res = None
    with open(stdout, "r") as in_f:
        for line in in_f:
            line = line.strip()
            if correct.match(line):
                assert res is None
                res = "correct"
            elif wrong.match(line):
                assert res is None
                res = "error"
            if error.search(line):
                res = "unknown"
                if label not in known_errors["nuxmv"]:
                    print("Found nuxmv ERROR in {}".format(stdout))
    if res is None:
        with open(stderr, "r") as in_f:
            for line in in_f:
                line = line.strip()
                if memout.search(line):
                    res = "memout"
                if res is not None:
                    break
    return res if res else "timeout"


def check_f3(stdout, stderr) -> str:
    assert os.path.isfile(stdout)
    assert os.path.isfile(stderr)
    assert stdout.endswith(".{}.stdout".format(tool2ext["f3"]))
    assert stderr.endswith(".{}.stderr".format(tool2ext["f3"]))
    label = os.path.basename(stdout)[:-len(".{}.stdout"
                                           .format(tool2ext["f3"]))]
    correct = re.compile(r"end\s+of\s+`.*`\s*:\s*SUCCESS")
    wrong = re.compile(r"end\s+of\s+`.*`\s*:\s*FAILURE")
    unknown = re.compile(r"end\s+of\s+`.*`\s*:\s*UNKNOWN")
    error = re.compile(r"(error)|(exception)|(attributeerror)",
                       re.IGNORECASE)
    res = None
    with open(stdout, "r") as in_f:
        for line in in_f:
            line = line.strip()
            if correct.match(line):
                assert res is None
                res = "correct"
            elif wrong.match(line):
                assert res is None
                res = "error"
            elif unknown.match(line):
                assert res is None
                res = "unknown"
            if error.search(line):
                res = "unknown"
                if label not in known_errors["f3"]:
                    print("Found F3 ERROR in {}".format(stdout))
    if res is None:
        with open(stderr, "r") as in_f:
            for line in in_f:
                line = line.strip()
                if error.search(line):
                    res = "unknown"
                    if label not in known_errors["f3"]:
                        print("Found F3 ERROR in {}".format(stdout))
    return res if res else "timeout"


def check_t2(stdout, stderr) -> str:
    assert os.path.isfile(stdout)
    assert os.path.isfile(stderr)
    assert stdout.endswith(".{}.stdout".format(tool2ext["t2"]))
    assert stderr.endswith(".{}.stderr".format(tool2ext["t2"]))
    label = os.path.basename(stdout)[:-len(".{}.stdout"
                                           .format(tool2ext["t2"]))]
    correct = re.compile(r"(Nontermination\s+proof\s+succeeded)|(Temporal\s+proof\s+failed)")
    wrong = re.compile(r"(Termination\s+proof\s+succeeded)|(Temporal\s+proof\s+succeeded)")
    unknown = re.compile(r"Termination/nontermination\s+proof\s+failed")
    error = re.compile(r"(error)|(exception)|(assert)", re.IGNORECASE)
    res = None
    with open(stdout, "r") as in_f:
        for line in in_f:
            line = line.strip()
            if correct.match(line):
                assert res is None
                res = "correct"
            elif wrong.match(line):
                assert res is None
                res = "error"
            elif unknown.match(line):
                assert res is None
                res = "unknown"
            if error.search(line):
                res = "unknown"
                if label not in known_errors["t2"]:
                    print("Found t2 ERROR in {}".format(stdout))
    return res if res else "timeout"


def check_ultimate(stdout, stderr) -> str:
    assert os.path.isfile(stdout)
    assert os.path.isfile(stderr)
    assert stdout.endswith(".{}.stdout".format(tool2ext["ultimate"]))
    assert stderr.endswith(".{}.stderr".format(tool2ext["ultimate"]))
    label = os.path.basename(stdout)[:-len(".{}.stdout"
                                           .format(tool2ext["ultimate"]))]
    correct = re.compile(r"(RESULT: Ultimate proved your program to be incorrect!)|(.*execution that violates the LTL property)")
    wrong = re.compile(r"(RESULT: Ultimate proved your program to be correct!)|(.*the\s+LTL\s+property.*holds)")
    unknown = re.compile(r".*Buchi Automizer is unable to decide")
    memout = re.compile(r"OutOfMemoryError")
    error = re.compile(r"Syntax error")
    res = None
    with open(stdout, "r") as in_f:
        for line in in_f:
            line = line.strip()
            if correct.match(line):
                # assert res is None or res == "correct", (res, stdout)
                res = "correct"
            elif wrong.match(line):
                assert res is None, res
                res = "error"
            elif unknown.match(line):
                # assert res is None, (res, stdout)
                res = "unknown"
            elif memout.search(line):
                res = "memout"
            if res is None and error.search(line):
                res = "error"

    if res == "error":
        res = "unknown"
        if label not in known_errors["ultimate"]:
            print("Found Ultimate ERROR in {}".format(stdout))
    return res if res else "memout"


def check_uppaal(stdout, stderr) -> str:
    assert os.path.isfile(stdout)
    assert os.path.isfile(stderr)
    assert stdout.endswith(".{}.stdout".format(tool2ext["uppaal"]))
    assert stderr.endswith(".{}.stderr".format(tool2ext["uppaal"]))
    label = os.path.basename(stdout)[:-len(".{}.stdout"
                                           .format(tool2ext["uppaal"]))]
    correct = re.compile(r".*Formula is NOT satisfied")
    wrong = re.compile(r".*Formula is satisfied")
    error = re.compile(r"(syntax error)|(undefined)", re.IGNORECASE)
    res = None
    with open(stdout, "r") as in_f:
        for line in in_f:
            line = line.strip()
            if correct.match(line):
                # assert res is None or res == "correct", (res, stdout)
                res = "correct"
            elif wrong.match(line):
                assert res is None, res
                res = "error"
            if res is None and error.search(line):
                res = "error"

    if res == "error":
        res = "unknown"
        if label not in known_errors["ultimate"]:
            print("Found Ultimate ERROR in {}".format(stdout))

    return res if res else "timeout"


tool2check_f = {
    "anant": check_anant,
    "aprove": check_aprove,
    "divine": check_divine,
    "mitlbmc": check_mitlbmc,
    "nuxmv": check_nuxmv,
    "f3": check_f3,
    "t2": check_t2,
    "ultimate": check_ultimate,
    "uppaal": check_uppaal
}


def parse_results(base_dir, tool_name):
    global TO

    tool_name = tool_name.lower()
    check_result = tool2check_f[tool_name]
    tool_ext = tool2ext[tool_name]
    results = {}
    bench_type = []
    for _d0 in os.listdir(base_dir):
        d0 = os.path.join(base_dir, _d0)
        if os.path.isdir(d0):
            for _d1 in os.listdir(d0):
                d1 = os.path.join(d0, _d1)
                if os.path.isdir(d1):
                    for stdout in sorted(glob("{}/**/*.stdout".format(d1),
                                              recursive=True)):
                        bench_type = []
                        stderr = stdout[:-len("stdout")] + "stderr"
                        stats = stdout[:-len("stdout")] + "stats"
                        assert os.path.isfile(stdout)
                        assert os.path.isfile(stderr)
                        assert os.path.isfile(stats)
                        stack = os.path.relpath(stdout, base_dir)
                        stack, label = os.path.split(stack)
                        label = label[:-len(".{}.stdout".format(tool_ext))]
                        assert label
                        while stack:
                            stack, last = os.path.split(stack)
                            last = last.lower()
                            if not (last.startswith(tool_name) or
                                    last.endswith(tool_name)):
                                if tool_name != "anant" or \
                                   not (last.startswith("t2") or
                                        last.endswith("t2")):
                                    bench_type.append(last)
                        bench_type = list(reversed(bench_type))

                        res = None
                        curr = results
                        for t in bench_type:
                            if curr.get(t) is None:
                                curr[t] = {}
                            curr = curr[t]
                        assert label not in curr, (label, curr)
                        exec_time = get_exec_time(stats)
                        if exec_time >= TO:
                            # assert res != "correct"
                            res = "timeout"
                        if res != "timeout":
                            res = check_result(stdout, stderr)
                        assert res in {"error", "timeout", "correct",
                                       "unknown", "memout"}
                        if res == "error" and \
                           label not in known_errors[tool_name]:
                            raise Exception("Error in: {}, {}"
                                            .format(label, bench_type))
                        curr[label] = (res, exec_time)
    return results


def getopts():
    p = argparse.ArgumentParser()
    p.add_argument('-ts', '--tools', type=str, nargs='+', default=None,
                   help="consider only given tools")
    p.add_argument('-in', '--in-results', type=str,
                   required=True,
                   help="results directory")
    return p.parse_args()


def main(opts):
    base_dir = opts.in_results
    assert os.path.isdir(base_dir)
    tools = opts.tools
    if tools is None:
        tools = []
        for t in os.listdir(base_dir):
            _t = os.path.join(base_dir, t)
            if os.path.isdir(_t) and t.endswith("_results"):
                t_name = t[:-len("_results")]
                tools.append(t_name)
    results = {}
    for t in tools:
        tool_dir = os.path.join(base_dir, "{}_results".format(t))
        assert os.path.isdir(tool_dir)
        results[t] = parse_results(tool_dir, t)
    import pdb
    pdb.set_trace()
    print(results)


if __name__ == "__main__":
    main(getopts())
