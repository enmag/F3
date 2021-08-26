#! /usr/bin/env python3

import os
import re
import argparse
import sys
from itertools import chain
from glob import glob

TO = 3600

tool2ext = {
    "anant": "t2",
    "aprove": "c",
    "divine": "xml",
    "irankfinder": "c",
    "mitlbmc": "tsmv",
    "nuxmv": "smv",
    "f3": "py",
    "oldf3": "py",
    "t2": "t2",
    "ultimate_term": "c",
    "ultimate_ltl": "c",
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
known_errors["aprove"] = frozenset(chain(
    # crashing thread
    ["15"],
    # wrong results
    (f"bakery_simple_bug_{str(i).zfill(4)}" for i in range(2, 31)),
    (f"semaphore_{str(i).zfill(4)}" for i in range(2, 14)),
    (f"critical_region_{str(i).zfill(4)}" for i in range(2, 14)),
    (f"csma_{str(i).zfill(4)}" for i in range(2, 17)),
    (f"fddi_{str(i).zfill(4)}" for i in range(2, 13)),
    (f"fischer_{str(i).zfill(4)}" for i in range(2, 31)),
    (f"lynch_protocol_{str(i).zfill(4)}" for i in range(2, 5)),
    (f"lynch_protocol_{str(i).zfill(4)}" for i in range(6, 19)),
    (f"train_gate_{str(i).zfill(4)}" for i in range(2, 25)),
    (f"csma_backoff_{str(i).zfill(4)}" for i in range(2, 14)),
    (f"dynamic_fischer_{str(i).zfill(4)}" for i in range(2, 20)),
    (f"dynamic_lynch_{str(i).zfill(4)}" for i in range(2, 14)),
    (f"token_ring_{str(i).zfill(4)}" for i in range(2, 15)),
    (f"token_ring_{str(i).zfill(4)}" for i in range(16, 28)),
    ["adaptive_cruise_control", "airbag_1", "airbag_2",
     "csma_backoff_single_station",
     "bouncing_ball_harmonic", "bouncing_ball_inc", "bouncing_ball_simple",
     "etcs", "extending_bound", "extending_bound_no_stutter", "nonlinear_reset",
     "sender_receiver",
     "synchronization_ttethernet_network0", "synchronization_ttethernet_network1",
     "tanks"],
    ["maxplus_12_0", "maxplus_12_11", "maxplus_12_12", "maxplus_12_13",
     "maxplus_12_14", "maxplus_12_16", "maxplus_12_19", "maxplus_12_22",
     "maxplus_12_23", "maxplus_12_25", "maxplus_12_27", "maxplus_12_29",
     "maxplus_12_2", "maxplus_12_30", "maxplus_12_32", "maxplus_12_34",
     "maxplus_12_35", "maxplus_12_38", "maxplus_12_41", "maxplus_12_44",
     "maxplus_12_45", "maxplus_12_47", "maxplus_12_51", "maxplus_12_52",
     "maxplus_12_53", "maxplus_12_54", "maxplus_12_57", "maxplus_12_58",
     "maxplus_12_5", "maxplus_12_65", "maxplus_12_67", "maxplus_12_68",
     "maxplus_12_69", "maxplus_12_6", "maxplus_12_70", "maxplus_12_71",
     "maxplus_12_72", "maxplus_12_74", "maxplus_12_77", "maxplus_12_78",
     "maxplus_12_79", "maxplus_12_7", "maxplus_12_81", "maxplus_12_85",
     "maxplus_12_86", "maxplus_12_87", "maxplus_12_8", "maxplus_12_91",
     "maxplus_12_92", "maxplus_12_96", "maxplus_12_97", "maxplus_12_98",
     "maxplus_12_9", "maxplus_16_0", "maxplus_16_12", "maxplus_16_13",
     "maxplus_16_14", "maxplus_16_15", "maxplus_16_16", "maxplus_16_17",
     "maxplus_16_19", "maxplus_16_21", "maxplus_16_22", "maxplus_16_23",
     "maxplus_16_25", "maxplus_16_27", "maxplus_16_28", "maxplus_16_29",
     "maxplus_16_2", "maxplus_16_30", "maxplus_16_34", "maxplus_16_35",
     "maxplus_16_36", "maxplus_16_38", "maxplus_16_39", "maxplus_16_41",
     "maxplus_16_43", "maxplus_16_44", "maxplus_16_45", "maxplus_16_47",
     "maxplus_16_51", "maxplus_16_53", "maxplus_16_54", "maxplus_16_57",
     "maxplus_16_58", "maxplus_16_5", "maxplus_16_65", "maxplus_16_67",
     "maxplus_16_68", "maxplus_16_6", "maxplus_16_70", "maxplus_16_71",
     "maxplus_16_72", "maxplus_16_74", "maxplus_16_76", "maxplus_16_77",
     "maxplus_16_78", "maxplus_16_79", "maxplus_16_7", "maxplus_16_80",
     "maxplus_16_81", "maxplus_16_85", "maxplus_16_86", "maxplus_16_89",
     "maxplus_16_8", "maxplus_16_90", "maxplus_16_91", "maxplus_16_92",
     "maxplus_16_93", "maxplus_16_96", "maxplus_16_97", "maxplus_16_9",
     "maxplus_20_0", "maxplus_20_11", "maxplus_20_12", "maxplus_20_13",
     "maxplus_20_14", "maxplus_20_16", "maxplus_20_19", "maxplus_20_21",
     "maxplus_20_22", "maxplus_20_23", "maxplus_20_25", "maxplus_20_27",
     "maxplus_20_29", "maxplus_20_2", "maxplus_20_30", "maxplus_20_34",
     "maxplus_20_35", "maxplus_20_36", "maxplus_20_38", "maxplus_20_39",
     "maxplus_20_41", "maxplus_20_44", "maxplus_20_45", "maxplus_20_47",
     "maxplus_20_53", "maxplus_20_54", "maxplus_20_57", "maxplus_20_58",
     "maxplus_20_5", "maxplus_20_65", "maxplus_20_68", "maxplus_20_69",
     "maxplus_20_6", "maxplus_20_70", "maxplus_20_71", "maxplus_20_72",
     "maxplus_20_74", "maxplus_20_77", "maxplus_20_78", "maxplus_20_79",
     "maxplus_20_7", "maxplus_20_80", "maxplus_20_81", "maxplus_20_85",
     "maxplus_20_86", "maxplus_20_87", "maxplus_20_89", "maxplus_20_8",
     "maxplus_20_91", "maxplus_20_92", "maxplus_20_96", "maxplus_20_97",
     "maxplus_20_98", "maxplus_20_9", "maxplus_24_0", "maxplus_24_11",
     "maxplus_24_12", "maxplus_24_13", "maxplus_24_14", "maxplus_24_16",
     "maxplus_24_17", "maxplus_24_19", "maxplus_24_21", "maxplus_24_22",
     "maxplus_24_23", "maxplus_24_25", "maxplus_24_27", "maxplus_24_28",
     "maxplus_24_29", "maxplus_24_2", "maxplus_24_30", "maxplus_24_34",
     "maxplus_24_35", "maxplus_24_36", "maxplus_24_38", "maxplus_24_39",
     "maxplus_24_41", "maxplus_24_44", "maxplus_24_45", "maxplus_24_47",
     "maxplus_24_51", "maxplus_24_52", "maxplus_24_53", "maxplus_24_54",
     "maxplus_24_57", "maxplus_24_58", "maxplus_24_5", "maxplus_24_65",
     "maxplus_24_67", "maxplus_24_68", "maxplus_24_69", "maxplus_24_6",
     "maxplus_24_70", "maxplus_24_71", "maxplus_24_72", "maxplus_24_74",
     "maxplus_24_76", "maxplus_24_77", "maxplus_24_78", "maxplus_24_79",
     "maxplus_24_7", "maxplus_24_80", "maxplus_24_81", "maxplus_24_86",
     "maxplus_24_87", "maxplus_24_8", "maxplus_24_90", "maxplus_24_91",
     "maxplus_24_92", "maxplus_24_93", "maxplus_24_96", "maxplus_24_97",
     "maxplus_24_98", "maxplus_24_9", "maxplus_28_0", "maxplus_28_11",
     "maxplus_28_12", "maxplus_28_13", "maxplus_28_14", "maxplus_28_15",
     "maxplus_28_16", "maxplus_28_17", "maxplus_28_19", "maxplus_28_21",
     "maxplus_28_22", "maxplus_28_23", "maxplus_28_25", "maxplus_28_27",
     "maxplus_28_28", "maxplus_28_29", "maxplus_28_2", "maxplus_28_30",
     "maxplus_28_32", "maxplus_28_34", "maxplus_28_35", "maxplus_28_36",
     "maxplus_28_38", "maxplus_28_39", "maxplus_28_41", "maxplus_28_43",
     "maxplus_28_44", "maxplus_28_45", "maxplus_28_47", "maxplus_28_52",
     "maxplus_28_53", "maxplus_28_54", "maxplus_28_57", "maxplus_28_58",
     "maxplus_28_5", "maxplus_28_65", "maxplus_28_67", "maxplus_28_68",
     "maxplus_28_69", "maxplus_28_6", "maxplus_28_70", "maxplus_28_71",
     "maxplus_28_72", "maxplus_28_74", "maxplus_28_76", "maxplus_28_77",
     "maxplus_28_78", "maxplus_28_79", "maxplus_28_7", "maxplus_28_80",
     "maxplus_28_81", "maxplus_28_85", "maxplus_28_86", "maxplus_28_87",
     "maxplus_28_89", "maxplus_28_8", "maxplus_28_90", "maxplus_28_91",
     "maxplus_28_92", "maxplus_28_93", "maxplus_28_96", "maxplus_28_97",
     "maxplus_28_98", "maxplus_28_9", "maxplus_32_0", "maxplus_32_11",
     "maxplus_32_12", "maxplus_32_13", "maxplus_32_14", "maxplus_32_15",
     "maxplus_32_16", "maxplus_32_17", "maxplus_32_19", "maxplus_32_21",
     "maxplus_32_22", "maxplus_32_23", "maxplus_32_25", "maxplus_32_27",
     "maxplus_32_28", "maxplus_32_29", "maxplus_32_2", "maxplus_32_30",
     "maxplus_32_32", "maxplus_32_34", "maxplus_32_35", "maxplus_32_36",
     "maxplus_32_38", "maxplus_32_39", "maxplus_32_41", "maxplus_32_44",
     "maxplus_32_45", "maxplus_32_47", "maxplus_32_52", "maxplus_32_53",
     "maxplus_32_54", "maxplus_32_57", "maxplus_32_58", "maxplus_32_5",
     "maxplus_32_65", "maxplus_32_67", "maxplus_32_68", "maxplus_32_69",
     "maxplus_32_6", "maxplus_32_70", "maxplus_32_71", "maxplus_32_72",
     "maxplus_32_74", "maxplus_32_76", "maxplus_32_77", "maxplus_32_78",
     "maxplus_32_79", "maxplus_32_7", "maxplus_32_80", "maxplus_32_81",
     "maxplus_32_85", "maxplus_32_86", "maxplus_32_87", "maxplus_32_89",
     "maxplus_32_8", "maxplus_32_90", "maxplus_32_91", "maxplus_32_92",
     "maxplus_32_93", "maxplus_32_96", "maxplus_32_97", "maxplus_32_98",
     "maxplus_32_9", "maxplus_36_0", "maxplus_36_11", "maxplus_36_12",
     "maxplus_36_13", "maxplus_36_14", "maxplus_36_15", "maxplus_36_16",
     "maxplus_36_17", "maxplus_36_19", "maxplus_36_21", "maxplus_36_22",
     "maxplus_36_23", "maxplus_36_25", "maxplus_36_27", "maxplus_36_28",
     "maxplus_36_29", "maxplus_36_2", "maxplus_36_30", "maxplus_36_32",
     "maxplus_36_34", "maxplus_36_35", "maxplus_36_36", "maxplus_36_38",
     "maxplus_36_39", "maxplus_36_41", "maxplus_36_44", "maxplus_36_45",
     "maxplus_36_47", "maxplus_36_52", "maxplus_36_53", "maxplus_36_54",
     "maxplus_36_57", "maxplus_36_58", "maxplus_36_5", "maxplus_36_65",
     "maxplus_36_67", "maxplus_36_68", "maxplus_36_6", "maxplus_36_70",
     "maxplus_36_71", "maxplus_36_72", "maxplus_36_74", "maxplus_36_76",
     "maxplus_36_77", "maxplus_36_78", "maxplus_36_79", "maxplus_36_7",
     "maxplus_36_80", "maxplus_36_81", "maxplus_36_85", "maxplus_36_86",
     "maxplus_36_87", "maxplus_36_8", "maxplus_36_90", "maxplus_36_92",
     "maxplus_36_93", "maxplus_36_96", "maxplus_36_97", "maxplus_36_98",
     "maxplus_36_9", "maxplus_40_0", "maxplus_40_11", "maxplus_40_12",
     "maxplus_40_13", "maxplus_40_14", "maxplus_40_15", "maxplus_40_16",
     "maxplus_40_17", "maxplus_40_19", "maxplus_40_21", "maxplus_40_22",
     "maxplus_40_23", "maxplus_40_25", "maxplus_40_27", "maxplus_40_28",
     "maxplus_40_29", "maxplus_40_2", "maxplus_40_30", "maxplus_40_34",
     "maxplus_40_35", "maxplus_40_36", "maxplus_40_38", "maxplus_40_39",
     "maxplus_40_41", "maxplus_40_44", "maxplus_40_45", "maxplus_40_47",
     "maxplus_40_51", "maxplus_40_52", "maxplus_40_53", "maxplus_40_54",
     "maxplus_40_57", "maxplus_40_58", "maxplus_40_5", "maxplus_40_65",
     "maxplus_40_67", "maxplus_40_68", "maxplus_40_69", "maxplus_40_6",
     "maxplus_40_70", "maxplus_40_71", "maxplus_40_72", "maxplus_40_74",
     "maxplus_40_76", "maxplus_40_77", "maxplus_40_78", "maxplus_40_79",
     "maxplus_40_7", "maxplus_40_80", "maxplus_40_81", "maxplus_40_85",
     "maxplus_40_86", "maxplus_40_87", "maxplus_40_89", "maxplus_40_8",
     "maxplus_40_90", "maxplus_40_91", "maxplus_40_92", "maxplus_40_93",
     "maxplus_40_96", "maxplus_40_97", "maxplus_40_98", "maxplus_40_9",
     "maxplus_4_12", "maxplus_4_14", "maxplus_4_17", "maxplus_4_18",
     "maxplus_4_22", "maxplus_4_23", "maxplus_4_27", "maxplus_4_28",
     "maxplus_4_33", "maxplus_4_36", "maxplus_4_38", "maxplus_4_3",
     "maxplus_4_40", "maxplus_4_44", "maxplus_4_45", "maxplus_4_51",
     "maxplus_4_52", "maxplus_4_53", "maxplus_4_58", "maxplus_4_67",
     "maxplus_4_69", "maxplus_4_72", "maxplus_4_78", "maxplus_4_90",
     "maxplus_4_93", "maxplus_4_96", "maxplus_4_99", "maxplus_8_0",
     "maxplus_8_12", "maxplus_8_13", "maxplus_8_14", "maxplus_8_16",
     "maxplus_8_19", "maxplus_8_21", "maxplus_8_22", "maxplus_8_23",
     "maxplus_8_25", "maxplus_8_27", "maxplus_8_29", "maxplus_8_2",
     "maxplus_8_30", "maxplus_8_34", "maxplus_8_35", "maxplus_8_36",
     "maxplus_8_38", "maxplus_8_39", "maxplus_8_41", "maxplus_8_43",
     "maxplus_8_44", "maxplus_8_45", "maxplus_8_47", "maxplus_8_51",
     "maxplus_8_52", "maxplus_8_54", "maxplus_8_57", "maxplus_8_58",
     "maxplus_8_5", "maxplus_8_65", "maxplus_8_68", "maxplus_8_69",
     "maxplus_8_6", "maxplus_8_70", "maxplus_8_71", "maxplus_8_72",
     "maxplus_8_74", "maxplus_8_77", "maxplus_8_78", "maxplus_8_7",
     "maxplus_8_81", "maxplus_8_86", "maxplus_8_89", "maxplus_8_8",
     "maxplus_8_93", "maxplus_8_96", "maxplus_8_97", "maxplus_8_9"]))
known_errors["divine"] = frozenset([])
known_errors["irankfinder"] = frozenset(chain(
    (f"bakery_simple_bug_{str(i).zfill(4)}" for i in range(18, 31)),
    (f"semaphore_{str(i).zfill(4)}" for i in range(8, 31)),
    (f"csma_{str(i).zfill(4)}" for i in range(20, 31)),
    (f"csma_backoff_{str(i).zfill(4)}" for i in range(23, 31)),
    (f"token_ring_{str(i).zfill(4)}" for i in range(22, 31))))
known_errors["f3"] = frozenset([])
known_errors["t2"] = frozenset([])
known_errors["ultimate_term"] = frozenset([
    # ultimate fails to parse them. Both GCC and CLANG compile them.
    "bouncing_ball_harmonic", "nonlinear_reset", "timed_extending_bound"])
known_errors["ultimate_ltl"] = frozenset([])


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
        raise Exception(f"Real time not found in {stats}")
    if u_time is None:
        raise Exception(f"User time not found in {stats}")
    if s_time is None:
        raise Exception(f"Sys time not found in {stats}")
    return max(r_time, u_time + s_time)


def check_anant(stdout, stderr) -> str:
    assert os.path.isfile(stdout)
    assert os.path.isfile(stderr)
    assert stdout.endswith(f".{tool2ext['anant']}.stdout")
    assert stderr.endswith(f".{tool2ext['anant']}.stderr")
    label = os.path.basename(stdout)[:-len(f".{tool2ext['anant']}.stdout")]
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
                    print(f"Found anant ERROR in {stdout}")
                # sys.exit(0)
    return res if res else "timeout"


def check_aprove(stdout, stderr) -> str:
    assert os.path.isfile(stdout)
    assert os.path.isfile(stderr)
    assert stdout.endswith(f".{tool2ext['aprove']}.stdout")
    assert stderr.endswith(f".{tool2ext['aprove']}.stderr")
    label = os.path.basename(stdout)[:-len(f".{tool2ext['aprove']}.stdout")]
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
                if label not in known_errors["aprove"]:
                    print(f"Found aprove ERROR in {stdout}")
                    raise Exception(f"Aprove wrong result: {stdout}")
                res = "unknown"
            elif unknown.match(line):
                assert res is None
                res = "unknown"
            elif memout.search(line):
                res = "memout"
            if error.search(line):
                res = "unknown"
                if label not in known_errors["aprove"]:
                    print(f"Found aprove ERROR in {stdout}")
    if res is None:
        with open(stderr, "r") as in_f:
            for line in in_f:
                line = line.strip()
                if memout.search(line):
                    res = "memout"
                elif error.search(line):
                    res = "unknown"
                    if label not in known_errors["aprove"]:
                        print(f"Found aprove ERROR in {stderr}")
                if res is not None:
                    break
    return res if res else "timeout"


def check_divine(stdout, stderr) -> str:
    assert os.path.isfile(stdout)
    assert os.path.isfile(stderr)
    assert stdout.endswith(f".{tool2ext['divine']}.stdout")
    assert stderr.endswith(f".{tool2ext['divine']}.stderr")
    label = os.path.basename(stdout)[:-len(f".{tool2ext['divine']}.stdout")]

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
        print(f"Found DIVINE ERROR in {stderr}")
        sys.exit(0)
    return res if res else "timeout"


def check_irankfinder(stdout, stderr) -> str:
    assert os.path.isfile(stdout)
    assert os.path.isfile(stderr)
    assert stdout.endswith(f".{tool2ext['irankfinder']}.stdout")
    assert stderr.endswith(f".{tool2ext['irankfinder']}.stderr")
    label = os.path.basename(stdout)[:-len(f".{tool2ext['irankfinder']}.stdout")]
    correct = re.compile(r"NO")
    wrong = re.compile(r"YES")
    unknown = re.compile(r"MAYBE")
    memout = re.compile(r"memout", re.IGNORECASE)
    error = re.compile(r"(exception)|(TIMEOUT)", re.IGNORECASE)
    res = None
    with open(stdout, "r") as in_f:
        for line in in_f:
            line = line.strip()
            if correct.match(line):
                assert res is None or res == "correct"
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
                if label not in known_errors["irankfinder"]:
                    print(f"Found irankfinder ERROR in {stdout}")
    if res is None:
        with open(stderr, "r") as in_f:
            for line in in_f:
                line = line.strip()
                if memout.search(line):
                    res = "memout"
                elif error.search(line):
                    res = "unknown"
                    if label not in known_errors["irankfinder"]:
                        print(f"Found irankfinder ERROR in {stderr}")
                if res is not None:
                    break
    return res if res else "timeout"


def check_mitlbmc(stdout, stderr) -> str:
    assert os.path.isfile(stdout)
    assert os.path.isfile(stderr)
    assert stdout.endswith(f".{tool2ext['mitlbmc']}.stdout")
    assert stderr.endswith(f".{tool2ext['mitlbmc']}.stderr")
    label = os.path.basename(stdout)[:-len(f".{tool2ext['mitlbmc']}.stdout")]
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
                    print(f"Found mitlbmc ERROR in {stdout}")
    return res if res else "timeout"


def check_nuxmv(stdout, stderr) -> str:
    assert os.path.isfile(stdout)
    assert os.path.isfile(stderr)
    assert stdout.endswith(f".{tool2ext['nuxmv']}.stdout")
    assert stderr.endswith(f".{tool2ext['nuxmv']}.stderr")
    label = os.path.basename(stdout)[:-len(f".{tool2ext['nuxmv']}.stdout")]
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
                    print(f"Found nuxmv ERROR in {stdout}")
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
    assert stdout.endswith(f".{tool2ext['f3']}.stdout")
    assert stderr.endswith(f".{tool2ext['f3']}.stderr")
    label = os.path.basename(stdout)[:-len(f".{tool2ext['f3']}.stdout")]
    correct = re.compile(r"end\s+of\s+`.*`\s*:\s*SUCCESS")
    wrong = re.compile(r"end\s+of\s+`.*`\s*:\s*FAILURE")
    unknown = re.compile(r"end\s+of\s+`.*`\s*:\s*UNKNOWN")
    error = re.compile(r"(error)|(exception)|(attributeerror)",
                       re.IGNORECASE)
    segfault = re.compile(r"segmentation", re.IGNORECASE)
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
                    print(f"Found F3 ERROR in {stdout}")
    if res is None:
        with open(stderr, "r") as in_f:
            for line in in_f:
                line = line.strip()
                if segfault.search(line):
                    res = "unknown"
                    if label not in known_errors["f3"]:
                        print(f"Found F3 segfault in {stderr}")
                if error.search(line):
                    res = "unknown"
                    if label not in known_errors["f3"]:
                        print(f"Found F3 ERROR in {stderr}")
    return res if res else "timeout"


def check_t2(stdout, stderr) -> str:
    assert os.path.isfile(stdout)
    assert os.path.isfile(stderr)
    assert stdout.endswith(f".{tool2ext['t2']}.stdout")
    assert stderr.endswith(f".{tool2ext['t2']}.stderr")
    label = os.path.basename(stdout)[:-len(f".{tool2ext['t2']}.stdout")]
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
                    print(f"Found t2 ERROR in {stdout}")
    return res if res else "timeout"


def check_ultimate_term(stdout, stderr) -> str:
    assert stdout.endswith(f".{tool2ext['ultimate_term']}.stdout")
    assert stderr.endswith(f".{tool2ext['ultimate_term']}.stderr")
    label = os.path.basename(stdout)[:-len(f".{tool2ext['ultimate_term']}.stdout")]
    res = check_ultimate(stdout, stderr)
    if res == "error":
        res = "unknown"
        if label not in known_errors["ultimate_term"]:
            print(f"Found Ultimate-term ERROR in {stdout}")
    return res

def check_ultimate_ltl(stdout, stderr) -> str:
    assert stdout.endswith(f".{tool2ext['ultimate_ltl']}.stdout")
    assert stderr.endswith(f".{tool2ext['ultimate_ltl']}.stderr")
    label = os.path.basename(stdout)[:-len(f".{tool2ext['ultimate_ltl']}.stdout")]
    res = check_ultimate(stdout, stderr)
    if res == "error":
        res = "unknown"
        if label not in known_errors["ultimate_ltl"]:
            print(f"Found Ultimate-LTL ERROR in {stdout}")
    return res


def check_ultimate(stdout, stderr) -> str:
    assert os.path.isfile(stdout)
    assert os.path.isfile(stderr)
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

    return res if res else "memout"


def check_uppaal(stdout, stderr) -> str:
    assert os.path.isfile(stdout)
    assert os.path.isfile(stderr)
    assert stdout.endswith(f".{tool2ext['uppaal']}.stdout")
    assert stderr.endswith(f".{tool2ext['uppaal']}.stderr")
    label = os.path.basename(stdout)[:-len(f".{tool2ext['uppaal']}.stdout")]
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
            print(f"Found Ultimate ERROR in {stdout}")

    return res if res else "timeout"


tool2check_f = {
    "anant": check_anant,
    "aprove": check_aprove,
    "divine": check_divine,
    "irankfinder": check_irankfinder,
    "mitlbmc": check_mitlbmc,
    "nuxmv": check_nuxmv,
    "f3": check_f3,
    "oldf3": check_f3,
    "t2": check_t2,
    "ultimate_term": check_ultimate_term,
    "ultimate_ltl": check_ultimate_ltl,
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
                    for stdout in sorted(glob(f"{d1}/**/*.stdout",
                                              recursive=True)):
                        bench_type = []
                        stderr = stdout[:-len("stdout")] + "stderr"
                        stats = stdout[:-len("stdout")] + "stats"
                        assert os.path.isfile(stdout)
                        assert os.path.isfile(stderr)
                        assert os.path.isfile(stats)
                        stack = os.path.relpath(stdout, base_dir)
                        stack, label = os.path.split(stack)
                        label = label[:-len(f".{tool_ext}.stdout")]
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
                            raise Exception(f"{tool_name} error in: {label}, {bench_type}")
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
        tool_dir = os.path.join(base_dir, f"{t}_results")
        assert os.path.isdir(tool_dir)
        results[t] = parse_results(tool_dir, t)
    import pdb
    pdb.set_trace()
    print(results)


if __name__ == "__main__":
    main(getopts())
