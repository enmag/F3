#! /usr/bin/env python3

from typing import Tuple
import os
import re
from itertools import chain
from glob import glob

from config import Config

# timeout in seconds.
TO = 3600
# memory limit in KB.
MEM_LIM = 31457280


class Resources:
    re_retval = re.compile(r"retval\s+(?P<num>\d+)")
    re_wc_time = re.compile(r"(?:(?:wall-clock time)|(?:real\s*:))\s+(?P<num>\d+(?:\.\d+)?)")
    re_usr_time = re.compile(r"(?:(?:usr time)|(?:user\s*:))\s+(?P<num>\d+(?:\.\d+)?)")
    re_sys_time = re.compile(r"(?:(?:sys time)|(?:sys\s*:))\s+(?P<num>\d+(?:\.\d+)?)")
    re_maxrss = re.compile(r"maximum resident set size\s+(?P<num>\d+)")
    re_ixrss = re.compile(r"(?<!un)shared memory size\s+(?P<num>\d+)")
    re_idrss = re.compile(r"unshared memory size\s+(?P<num>\d+)")
    re_isrss = re.compile(r"unshared stack size\s+(?P<num>\d+)")
    re_minflt = re.compile(r"page faults not requiring I/O\s+(?P<num>\d+)")
    re_majflt = re.compile(r"page faults requiring I/O\s+(?P<num>\d+)")
    re_nswap = re.compile(r"number of swap outs\s+(?P<num>\d+)")
    re_inblock = re.compile(r"block input operations\s+(?P<num>\d+)")
    re_oublock = re.compile(r"block output operations\s+(?P<num>\d+)")
    re_msgsnd = re.compile(r"messages sent\s+(?P<num>\d+)")
    re_msgrcv = re.compile(r"messages received\s+(?P<num>\d+)")
    re_nsignals = re.compile(r"signals received\s+(?P<num>\d+)")
    re_nvcsw = re.compile(r"(?<!in)voluntary context switches\s+(?P<num>\d+)")
    re_nivcsw = re.compile(r"involuntary context switches\s+(?P<num>\d+)")

    all_re = [re_retval, re_wc_time, re_usr_time, re_sys_time, re_maxrss,
              re_ixrss, re_idrss, re_minflt, re_majflt, re_nswap,
              re_inblock, re_oublock, re_msgsnd, re_msgrcv, re_nsignals,
              re_nvcsw, re_nivcsw]
    labels = ["retval", "wc_time", "usr_time", "sys_time", "maxrss",
              "ixrss", "idrss", "minflt", "majflt", "nswap",
              "inblock", "oublock", "msgsnd", "msgrcv", "nsignals",
              "nvcsw", "nivcsw"]
    f2idx = {lbl: idx for idx, lbl in enumerate(labels)}

    @staticmethod
    def from_lines(lines):
        assert len(Resources.labels) == len(Resources.f2idx)
        assert len(Resources.labels) == len(Resources.all_re)
        res = Resources()
        for line in reversed(lines):
            line = line.strip()
            if not line:
                continue
            for lbl, reg in zip(Resources.labels, Resources.all_re):
                assert lbl in Resources.f2idx
                idx = Resources.f2idx[lbl]
                match = reg.search(line)
                if match is not None:
                    assert "num" in match.groupdict()
                    match = match.groupdict()["num"]
                    assert match is not None and len(match) > 0, f"{lbl}, {match}: {line}"
                    val = float(match) if "." in match else int(match)
                    assert res.get_field(idx) is None, f"{lbl}, old: {res.get_field(idx)}, new: {val}"
                    res.set_field(idx, val)
                    break
            if res.is_complete():
                break
        return res

    def __init__(self):
        self._fields = [None for _ in Resources.all_re]

    def get_field(self, idx):
        if isinstance(idx, str):
            assert idx in Resources.f2idx
            idx = Resources.f2idx[idx]
        assert 0 <= idx < len(self._fields)
        return self._fields[idx]

    def set_field(self, idx, val):
        if isinstance(idx, str):
            assert idx in Resources.f2idx
            idx = Resources.f2idx[idx]
        assert 0 <= idx < len(self._fields)
        assert isinstance(val, (int, float))
        self._fields[idx] = val

    def is_complete(self):
        return all(field is not None for field in self._fields)

    @property
    def retval(self):
        return self.get_field("retval")

    @retval.setter
    def retval(self, val):
        self.set_field("retval", val)

    @property
    def wc_time(self):
        return self.get_field("wc_time")

    @wc_time.setter
    def wc_time(self, val):
        self.set_field("wc_time", val)

    @property
    def usr_time(self):
        return self.get_field("usr_time")

    @usr_time.setter
    def usr_time(self, val):
        self.set_field("usr_time", val)

    @property
    def sys_time(self):
        return self.get_field("sys_time")

    @sys_time.setter
    def sys_time(self, val):
        self.set_field("sys_time", val)

    @property
    def maxrss(self):
        return self.get_field("maxrss")

    @maxrss.setter
    def maxrss(self, val):
        self.set_field("maxrss", val)

    @property
    def ixrss(self):
        return self.get_field("ixrss")

    @ixrss.setter
    def ixrss(self, val):
        self.set_field("ixrss", val)

    @property
    def idrss(self):
        return self.get_field("idrss")

    @property
    def minflt(self):
        return self.get_field("minflt")

    @property
    def majflt(self):
        return self.get_field("majflt")

    @property
    def nswap(self):
        return self.get_field("nswap")

    @property
    def inblock(self):
        return self.get_field("inblock")

    @property
    def oublock(self):
        return self.get_field("oublock")

    @property
    def msgsnd(self):
        return self.get_field("msgsnd")

    @property
    def msgrcv(self):
        return self.get_field("msgrcv")

    @property
    def nsignals(self):
        return self.get_field("nsignals")

    @property
    def nvcsw(self):
        return self.get_field("nvcsw")

    @property
    def nivcsw(self):
        return self.get_field("nivcsw")


tool2ext = {
    "anant": "t2",
    "aprove": "c",
    "atmoc": "tsmv",
    "ctav": "xml",
    "divine": "xml",
    "irankfinder": "c",
    "ltsmin": "xml",
    # "mitlbmc": "tsmv",
    "nuxmv": "smv",
    "nuxmvbmc": "smv",
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
    # internal error.
    ["maxplus_12_1", "maxplus_12_10", "maxplus_12_18", "maxplus_12_20",
     "maxplus_12_24", "maxplus_12_26", "maxplus_12_31", "maxplus_12_37",
     "maxplus_12_42", "maxplus_12_48", "maxplus_12_49", "maxplus_12_50",
     "maxplus_12_56", "maxplus_12_60", "maxplus_12_61", "maxplus_12_63",
     "maxplus_12_66", "maxplus_12_73", "maxplus_12_82", "maxplus_12_83",
     "maxplus_12_95", "maxplus_12_99", "maxplus_16_1", "maxplus_16_18",
     "maxplus_16_20", "maxplus_16_24", "maxplus_16_26", "maxplus_16_31",
     "maxplus_16_32", "maxplus_16_33", "maxplus_16_37", "maxplus_16_46",
     "maxplus_16_48", "maxplus_16_49", "maxplus_16_50", "maxplus_16_59",
     "maxplus_16_60", "maxplus_16_61", "maxplus_16_62", "maxplus_16_63",
     "maxplus_16_66", "maxplus_16_73", "maxplus_16_75", "maxplus_16_94",
     "maxplus_16_95", "maxplus_16_99", "maxplus_20_1", "maxplus_20_24",
     "maxplus_20_28", "maxplus_20_31", "maxplus_20_32", "maxplus_20_4",
     "maxplus_20_43", "maxplus_20_56", "maxplus_20_59", "maxplus_20_60",
     "maxplus_20_61", "maxplus_20_62", "maxplus_20_63", "maxplus_20_75",
     "maxplus_20_84", "maxplus_20_94", "maxplus_20_95", "maxplus_20_99",
     "maxplus_24_24", "maxplus_24_26", "maxplus_24_31", "maxplus_24_40",
     "maxplus_24_49", "maxplus_24_66", "maxplus_24_84", "maxplus_28_37",
     "maxplus_28_50", "maxplus_32_24", "maxplus_8_1", "maxplus_8_10",
     "maxplus_8_18", "maxplus_8_20", "maxplus_8_24", "maxplus_8_26",
     "maxplus_8_28", "maxplus_8_3", "maxplus_8_31", "maxplus_8_32",
     "maxplus_8_33", "maxplus_8_37", "maxplus_8_46", "maxplus_8_49",
     "maxplus_8_50", "maxplus_8_55", "maxplus_8_63", "maxplus_8_64",
     "maxplus_8_66", "maxplus_8_67", "maxplus_8_75", "maxplus_8_82",
     "maxplus_8_83", "maxplus_8_84", "maxplus_8_94", "maxplus_8_95",
     "maxplus_8_99"],
    # wrong results
    (f"bakery_simple_bug_{str(i).zfill(4)}" for i in range(2, 31)),
    (f"semaphore_{str(i).zfill(4)}" for i in range(2, 14)),
    (f"critical_region_{str(i).zfill(4)}" for i in range(2, 14)),
    (f"csma_{str(i).zfill(4)}" for i in range(2, 17)),
    (f"fddi_{str(i).zfill(4)}" for i in range(2, 13)),
    (f"fischer_{str(i).zfill(4)}" for i in range(2, 31)),
    (f"lynch_protocol_{str(i).zfill(4)}" for i in range(2, 6)),
    (f"lynch_protocol_{str(i).zfill(4)}" for i in range(6, 18)),
    (f"train_gate_{str(i).zfill(4)}" for i in range(2, 25)),
    (f"csma_backoff_{str(i).zfill(4)}" for i in range(2, 14)),
    (f"dynamic_fischer_{str(i).zfill(4)}" for i in range(2, 20)),
    (f"dynamic_lynch_{str(i).zfill(4)}" for i in range(2, 14)),
    (f"token_ring_{str(i).zfill(4)}" for i in range(2, 28)),
    ["adaptive_cruise_control", "airbag_1", "airbag_2",
     "csma_backoff_single_station", "bouncing_ball_harmonic",
     "bouncing_ball_inc", "bouncing_ball_simple", "bouncing_ball_dec",
     "etcs", "extending_bound", "extending_bound_no_stutter",
     "nonlinear_reset", "sender_receiver", "synchronization_ttethernet_network0",
     "synchronization_ttethernet_network1", "tanks"],
    ["maxplus_12_0", "maxplus_12_11", "maxplus_12_12", "maxplus_12_13",
     "maxplus_12_14", "maxplus_12_16", "maxplus_12_19", "maxplus_12_2",
     "maxplus_12_22", "maxplus_12_23", "maxplus_12_25", "maxplus_12_27",
     "maxplus_12_29", "maxplus_12_30", "maxplus_12_32", "maxplus_12_34",
     "maxplus_12_35", "maxplus_12_38", "maxplus_12_41", "maxplus_12_44",
     "maxplus_12_45", "maxplus_12_47", "maxplus_12_5", "maxplus_12_51",
     "maxplus_12_52", "maxplus_12_53", "maxplus_12_54", "maxplus_12_57",
     "maxplus_12_58", "maxplus_12_6", "maxplus_12_65", "maxplus_12_67",
     "maxplus_12_68", "maxplus_12_69", "maxplus_12_7", "maxplus_12_70",
     "maxplus_12_71", "maxplus_12_72", "maxplus_12_74", "maxplus_12_77",
     "maxplus_12_78", "maxplus_12_79", "maxplus_12_8", "maxplus_12_81",
     "maxplus_12_85", "maxplus_12_86", "maxplus_12_87", "maxplus_12_9",
     "maxplus_12_91", "maxplus_12_92", "maxplus_12_96", "maxplus_12_97",
     "maxplus_12_98", "maxplus_16_0", "maxplus_16_12", "maxplus_16_13",
     "maxplus_16_14", "maxplus_16_15", "maxplus_16_16", "maxplus_16_17",
     "maxplus_16_19", "maxplus_16_2", "maxplus_16_21", "maxplus_16_22",
     "maxplus_16_23", "maxplus_16_25", "maxplus_16_27", "maxplus_16_28",
     "maxplus_16_29", "maxplus_16_30", "maxplus_16_34", "maxplus_16_35",
     "maxplus_16_36", "maxplus_16_38", "maxplus_16_39", "maxplus_16_41",
     "maxplus_16_43", "maxplus_16_44", "maxplus_16_45", "maxplus_16_47",
     "maxplus_16_5", "maxplus_16_51", "maxplus_16_53", "maxplus_16_54",
     "maxplus_16_57", "maxplus_16_58", "maxplus_16_6", "maxplus_16_65",
     "maxplus_16_67", "maxplus_16_68", "maxplus_16_7", "maxplus_16_70",
     "maxplus_16_71", "maxplus_16_72", "maxplus_16_74", "maxplus_16_76",
     "maxplus_16_77", "maxplus_16_78", "maxplus_16_79", "maxplus_16_8",
     "maxplus_16_80", "maxplus_16_81", "maxplus_16_85", "maxplus_16_86",
     "maxplus_16_89", "maxplus_16_9", "maxplus_16_90", "maxplus_16_91",
     "maxplus_16_92", "maxplus_16_93", "maxplus_16_96", "maxplus_16_97",
     "maxplus_20_0", "maxplus_20_11", "maxplus_20_12", "maxplus_20_13",
     "maxplus_20_14", "maxplus_20_16", "maxplus_20_19", "maxplus_20_2",
     "maxplus_20_21", "maxplus_20_22", "maxplus_20_23", "maxplus_20_25",
     "maxplus_20_27", "maxplus_20_29", "maxplus_20_30", "maxplus_20_34",
     "maxplus_20_35", "maxplus_20_36", "maxplus_20_38", "maxplus_20_39",
     "maxplus_20_41", "maxplus_20_44", "maxplus_20_45", "maxplus_20_47",
     "maxplus_20_5", "maxplus_20_53", "maxplus_20_54", "maxplus_20_57",
     "maxplus_20_58", "maxplus_20_6", "maxplus_20_65", "maxplus_20_68",
     "maxplus_20_69", "maxplus_20_7", "maxplus_20_70", "maxplus_20_71",
     "maxplus_20_72", "maxplus_20_74", "maxplus_20_77", "maxplus_20_78",
     "maxplus_20_79", "maxplus_20_8", "maxplus_20_80", "maxplus_20_81",
     "maxplus_20_85", "maxplus_20_86", "maxplus_20_87", "maxplus_20_89",
     "maxplus_20_9", "maxplus_20_91", "maxplus_20_92", "maxplus_20_96",
     "maxplus_20_97", "maxplus_20_98", "maxplus_24_0", "maxplus_24_11",
     "maxplus_24_12", "maxplus_24_13", "maxplus_24_14", "maxplus_24_16",
     "maxplus_24_17", "maxplus_24_19", "maxplus_24_2", "maxplus_24_21",
     "maxplus_24_22", "maxplus_24_23", "maxplus_24_25", "maxplus_24_27",
     "maxplus_24_28", "maxplus_24_29", "maxplus_24_30", "maxplus_24_34",
     "maxplus_24_35", "maxplus_24_36", "maxplus_24_38", "maxplus_24_39",
     "maxplus_24_41", "maxplus_24_44", "maxplus_24_45", "maxplus_24_47",
     "maxplus_24_5", "maxplus_24_51", "maxplus_24_52", "maxplus_24_53",
     "maxplus_24_54", "maxplus_24_57", "maxplus_24_58", "maxplus_24_6",
     "maxplus_24_65", "maxplus_24_67", "maxplus_24_68", "maxplus_24_69",
     "maxplus_24_7", "maxplus_24_70", "maxplus_24_71", "maxplus_24_72",
     "maxplus_24_74", "maxplus_24_76", "maxplus_24_77", "maxplus_24_78",
     "maxplus_24_79", "maxplus_24_8", "maxplus_24_80", "maxplus_24_81",
     "maxplus_24_86", "maxplus_24_87", "maxplus_24_9", "maxplus_24_90",
     "maxplus_24_91", "maxplus_24_92", "maxplus_24_93", "maxplus_24_96",
     "maxplus_24_97", "maxplus_24_98", "maxplus_28_0", "maxplus_28_11",
     "maxplus_28_12", "maxplus_28_13", "maxplus_28_14", "maxplus_28_15",
     "maxplus_28_16", "maxplus_28_17", "maxplus_28_19", "maxplus_28_2",
     "maxplus_28_21", "maxplus_28_22", "maxplus_28_23", "maxplus_28_25",
     "maxplus_28_27", "maxplus_28_28", "maxplus_28_29", "maxplus_28_30",
     "maxplus_28_32", "maxplus_28_34", "maxplus_28_35", "maxplus_28_36",
     "maxplus_28_38", "maxplus_28_39", "maxplus_28_41", "maxplus_28_43",
     "maxplus_28_44", "maxplus_28_45", "maxplus_28_47", "maxplus_28_5",
     "maxplus_28_52", "maxplus_28_53", "maxplus_28_54", "maxplus_28_57",
     "maxplus_28_58", "maxplus_28_6", "maxplus_28_65", "maxplus_28_67",
     "maxplus_28_68", "maxplus_28_69", "maxplus_28_7", "maxplus_28_70",
     "maxplus_28_71", "maxplus_28_72", "maxplus_28_74", "maxplus_28_76",
     "maxplus_28_77", "maxplus_28_78", "maxplus_28_79", "maxplus_28_8",
     "maxplus_28_80", "maxplus_28_81", "maxplus_28_85", "maxplus_28_86",
     "maxplus_28_87", "maxplus_28_89", "maxplus_28_9", "maxplus_28_90",
     "maxplus_28_91", "maxplus_28_92", "maxplus_28_93", "maxplus_28_96",
     "maxplus_28_97", "maxplus_28_98", "maxplus_32_0", "maxplus_32_11",
     "maxplus_32_12", "maxplus_32_13", "maxplus_32_14", "maxplus_32_15",
     "maxplus_32_16", "maxplus_32_17", "maxplus_32_19", "maxplus_32_2",
     "maxplus_32_21", "maxplus_32_22", "maxplus_32_23", "maxplus_32_25",
     "maxplus_32_27", "maxplus_32_28", "maxplus_32_29", "maxplus_32_30",
     "maxplus_32_32", "maxplus_32_34", "maxplus_32_35", "maxplus_32_36",
     "maxplus_32_38", "maxplus_32_39", "maxplus_32_41", "maxplus_32_44",
     "maxplus_32_45", "maxplus_32_47", "maxplus_32_5", "maxplus_32_52",
     "maxplus_32_53", "maxplus_32_54", "maxplus_32_57", "maxplus_32_58",
     "maxplus_32_6", "maxplus_32_65", "maxplus_32_67", "maxplus_32_68",
     "maxplus_32_69", "maxplus_32_7", "maxplus_32_70", "maxplus_32_71",
     "maxplus_32_72", "maxplus_32_74", "maxplus_32_76", "maxplus_32_77",
     "maxplus_32_78", "maxplus_32_79", "maxplus_32_8", "maxplus_32_80",
     "maxplus_32_81", "maxplus_32_85", "maxplus_32_86", "maxplus_32_87",
     "maxplus_32_89", "maxplus_32_9", "maxplus_32_90", "maxplus_32_91",
     "maxplus_32_92", "maxplus_32_93", "maxplus_32_96", "maxplus_32_97",
     "maxplus_32_98", "maxplus_36_0", "maxplus_36_11", "maxplus_36_12",
     "maxplus_36_13", "maxplus_36_14", "maxplus_36_15", "maxplus_36_16",
     "maxplus_36_17", "maxplus_36_19", "maxplus_36_2", "maxplus_36_21",
     "maxplus_36_22", "maxplus_36_23", "maxplus_36_25", "maxplus_36_27",
     "maxplus_36_28", "maxplus_36_29", "maxplus_36_30", "maxplus_36_32",
     "maxplus_36_34", "maxplus_36_35", "maxplus_36_36", "maxplus_36_38",
     "maxplus_36_39", "maxplus_36_41", "maxplus_36_44", "maxplus_36_45",
     "maxplus_36_47", "maxplus_36_5", "maxplus_36_52", "maxplus_36_53",
     "maxplus_36_54", "maxplus_36_57", "maxplus_36_58", "maxplus_36_6",
     "maxplus_36_65", "maxplus_36_67", "maxplus_36_68", "maxplus_36_7",
     "maxplus_36_70", "maxplus_36_71", "maxplus_36_72", "maxplus_36_74",
     "maxplus_36_76", "maxplus_36_77", "maxplus_36_78", "maxplus_36_79",
     "maxplus_36_8", "maxplus_36_80", "maxplus_36_81", "maxplus_36_85",
     "maxplus_36_86", "maxplus_36_87", "maxplus_36_9", "maxplus_36_90",
     "maxplus_36_92", "maxplus_36_93", "maxplus_36_96", "maxplus_36_97",
     "maxplus_36_98", "maxplus_40_0", "maxplus_40_11", "maxplus_40_12",
     "maxplus_40_13", "maxplus_40_14", "maxplus_40_15", "maxplus_40_16",
     "maxplus_40_17", "maxplus_40_19", "maxplus_40_2", "maxplus_40_21",
     "maxplus_40_22", "maxplus_40_23", "maxplus_40_25", "maxplus_40_27",
     "maxplus_40_28", "maxplus_40_29", "maxplus_40_30", "maxplus_40_34",
     "maxplus_40_35", "maxplus_40_36", "maxplus_40_38", "maxplus_40_39",
     "maxplus_40_41", "maxplus_40_44", "maxplus_40_45", "maxplus_40_47",
     "maxplus_40_5", "maxplus_40_51", "maxplus_40_52", "maxplus_40_53",
     "maxplus_40_54", "maxplus_40_57", "maxplus_40_58", "maxplus_40_6",
     "maxplus_40_65", "maxplus_40_67", "maxplus_40_68", "maxplus_40_69",
     "maxplus_40_7", "maxplus_40_70", "maxplus_40_71", "maxplus_40_72",
     "maxplus_40_74", "maxplus_40_76", "maxplus_40_77", "maxplus_40_78",
     "maxplus_40_79", "maxplus_40_8", "maxplus_40_80", "maxplus_40_81",
     "maxplus_40_85", "maxplus_40_86", "maxplus_40_87", "maxplus_40_89",
     "maxplus_40_9", "maxplus_40_90", "maxplus_40_91", "maxplus_40_92",
     "maxplus_40_93", "maxplus_40_96", "maxplus_40_97", "maxplus_40_98",
     "maxplus_4_12", "maxplus_4_14", "maxplus_4_17", "maxplus_4_18",
     "maxplus_4_22", "maxplus_4_23", "maxplus_4_27", "maxplus_4_28",
     "maxplus_4_3", "maxplus_4_33", "maxplus_4_36", "maxplus_4_38",
     "maxplus_4_40", "maxplus_4_44", "maxplus_4_45", "maxplus_4_51",
     "maxplus_4_52", "maxplus_4_53", "maxplus_4_58", "maxplus_4_67",
     "maxplus_4_69", "maxplus_4_72", "maxplus_4_78", "maxplus_4_90",
     "maxplus_4_93", "maxplus_4_96", "maxplus_4_99", "maxplus_8_0",
     "maxplus_8_12", "maxplus_8_13", "maxplus_8_14", "maxplus_8_16",
     "maxplus_8_19", "maxplus_8_2", "maxplus_8_21", "maxplus_8_22",
     "maxplus_8_23", "maxplus_8_25", "maxplus_8_27", "maxplus_8_29",
     "maxplus_8_30", "maxplus_8_34", "maxplus_8_35", "maxplus_8_36",
     "maxplus_8_38", "maxplus_8_39", "maxplus_8_41", "maxplus_8_43",
     "maxplus_8_44", "maxplus_8_45", "maxplus_8_47", "maxplus_8_5",
     "maxplus_8_51", "maxplus_8_52", "maxplus_8_54", "maxplus_8_57",
     "maxplus_8_58", "maxplus_8_6", "maxplus_8_65", "maxplus_8_68",
     "maxplus_8_69", "maxplus_8_7", "maxplus_8_70", "maxplus_8_71",
     "maxplus_8_72", "maxplus_8_74", "maxplus_8_77", "maxplus_8_78",
     "maxplus_8_8", "maxplus_8_81", "maxplus_8_86", "maxplus_8_89",
     "maxplus_8_9", "maxplus_8_93", "maxplus_8_96", "maxplus_8_97"]
))
known_errors["atmoc"] = frozenset([])
known_errors["ctav"] = frozenset([])
known_errors["divine"] = frozenset([])
known_errors["f3"] = frozenset([])
known_errors["irankfinder"] = frozenset(chain(
    (f"bakery_simple_bug_{str(i).zfill(4)}" for i in range(18, 31)),
    (f"semaphore_{str(i).zfill(4)}" for i in range(7, 31)),
    (f"csma_{str(i).zfill(4)}" for i in range(20, 31)),
    (f"csma_backoff_{str(i).zfill(4)}" for i in range(23, 31)),
    (f"token_ring_{str(i).zfill(4)}" for i in range(22, 31))
))
known_errors["ltsmin"] = frozenset([])
known_errors["nuxmv"] = frozenset([])
known_errors["nuxmvbmc"] = frozenset([])
known_errors["t2"] = frozenset([])
known_errors["ultimate_term"] = frozenset([
    # ultimate fails to parse them. Both GCC and CLANG compile them.
    "bouncing_ball_harmonic", "nonlinear_reset", "timed_extending_bound"])
known_errors["ultimate_ltl"] = frozenset([])
known_errors["uppaal"] = frozenset([])


def parse_resources(in_f) -> Resources:
    with open(in_f, 'r', encoding='utf-8', errors='replace') as in_stream:
        lines = in_stream.readlines()
    res = Resources.from_lines(lines)
    return res


def get_exec_time(stats) -> Tuple[float, float, float]:
    assert os.path.isfile(stats)
    real_time_re = re.compile(r"real\s*:\s+(?P<num>\d+(\.\d+)?)")
    user_time_re = re.compile(r"user\s*:\s+(?P<num>\d+(\.\d+)?)")
    sys_time_re = re.compile(r"sys\s*:\s+(?P<num>\d+(\.\d+)?)")
    r_time = None
    u_time = None
    s_time = None
    with open(stats, 'r', encoding='utf-8', errors='replace') as in_f:
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
    return r_time, u_time, s_time
    # return max(r_time, u_time + s_time)


def check_anant(stdout, stderr, expected_res) -> str:
    assert os.path.isfile(stdout)
    assert os.path.isfile(stderr)
    assert stdout.endswith(f".{tool2ext['anant']}.stdout")
    assert stderr.endswith(f".{tool2ext['anant']}.stderr")
    assert expected_res is False
    label = os.path.basename(stdout)[:-len(f".{tool2ext['anant']}.stdout")]
    correct = re.compile(r"Result\s*:\s*Non-Terminating")
    wrong = re.compile(r"Result\s*:\s*Terminating")
    unknown = re.compile(r"Result\s*:\s*Unknown")
    error = re.compile(r"error", re.IGNORECASE)
    res = None
    with open(stdout, 'r', encoding='utf-8', errors='replace') as in_f:
        for line in in_f:
            line = line.strip()
            if correct.match(line):
                assert res is None
                res = "correct"
            elif wrong.match(line):
                assert res is None
                res = "wrong"
            elif unknown.match(line):
                assert res is None
                res = "unknown"
            if error.search(line):
                res = "error"
    if res is None:
        res = "none"
    if res in {"none", "error", "wrong"}:
        if label not in known_errors["anant"]:
            print(f"Found anant {res.upper()} in {stdout}")
            res = "error"
        else:
            res = "unknown"
    return res


def check_aprove(stdout, stderr, expected_res) -> str:
    assert os.path.isfile(stdout)
    assert os.path.isfile(stderr)
    assert stdout.endswith(f".{tool2ext['aprove']}.stdout")
    assert stderr.endswith(f".{tool2ext['aprove']}.stderr")
    assert expected_res is False
    label = os.path.basename(stdout)[:-len(f".{tool2ext['aprove']}.stdout")]
    correct = re.compile(r"NO")
    wrong = re.compile(r"YES")
    unknown = re.compile(r"MAYBE")
    memout = re.compile(r"(OutOfMemoryError)|(insufficient memory for the Java Runtime Environment to continue)", re.IGNORECASE)
    error = re.compile(r"(exception)|(TIMEOUT)", re.IGNORECASE)
    res = None
    with open(stdout, 'r', encoding='utf-8', errors='replace') as in_f:
        for line in in_f:
            line = line.strip()
            if correct.match(line):
                assert res is None
                res = "correct"
            elif wrong.match(line):
                assert res is None
                res = "wrong"
            elif unknown.match(line):
                assert res is None
                res = "unknown"
            elif memout.search(line):
                assert res is None
                res = "memout"
            if error.search(line):
                res = "error"

    if res is None:
        with open(stderr, 'r', encoding='utf-8', errors='replace') as in_f:
            for line in in_f:
                line = line.strip()
                if memout.search(line):
                    res = "memout"
                elif error.search(line):
                    res = "error"
                if res is not None:
                    break
    if res is None:
        res = "none"
    if res in {"none", "error", "wrong"}:
        if label not in known_errors["aprove"]:
            print(f"Found aprove {res.upper()} in {stdout}")
            res = "error"
        else:
            res = "unknown"
    return res


def check_atmoc(stdout, stderr, expected_res) -> str:
    assert os.path.isfile(stdout)
    assert os.path.isfile(stderr)
    assert stdout.endswith(f".{tool2ext['atmoc']}.stdout")
    assert stderr.endswith(f".{tool2ext['atmoc']}.stderr")
    label = os.path.basename(stdout)[:-len(f".{tool2ext['atmoc']}.stdout")]
    if expected_res is True:
        wrong = re.compile(r"Property\s+\d+\s+.*does\s+not\s+hold")
        correct = re.compile(r"Property\s+\d+\s+.*holds")
    else:
        correct = re.compile(r"Property\s+\d+\s+.*does\s+not\s+hold")
        wrong = re.compile(r"Property\s+\d+\s+.*holds")
    error = re.compile(r"(\s+error\s+)|(exception)|(Exception)|(cannot open)|(must be built)",
                       re.IGNORECASE)
    res = None
    with open(stdout, 'r', encoding='utf-8', errors='replace') as in_f:
        for line in in_f:
            line = line.strip()
            if correct.match(line):
                assert res is None
                res = "correct"
            elif wrong.match(line):
                assert res is None
                res = "wrong"
            if error.search(line):
                res = "error"
    if res is None:
        res = "none"
    if res in {"none", "error", "wrong"}:
        if label not in known_errors["atmoc"]:
            print(f"Found ATMOC {res.upper()} in {stdout}")
            res = "error"
        else:
            res = "unknown"
    return res


def check_ctav(stdout, stderr, expected_res) -> str:
    assert os.path.isfile(stdout)
    assert os.path.isfile(stderr)
    assert stdout.endswith(f".{tool2ext['ctav']}.stdout")
    assert stderr.endswith(f".{tool2ext['ctav']}.stderr")
    label = os.path.basename(stdout)[:-len(f".{tool2ext['ctav']}.stdout")]
    if expected_res is True:
        wrong = re.compile(r"A counter example is found, the property is not TRUE!")
        correct = re.compile(r"No counter example is found, the property is TRUE!")
    else:
        correct = re.compile(r"A counter example is found, the property is not TRUE!")
        wrong = re.compile(r"No counter example is found, the property is TRUE!")
    memout = re.compile(r"Out of memory")
    timeout = re.compile(r"Killed")
    error = re.compile(r"(\s+error\s+)|(exception)|(Exception)|(cannot open)|"
                       r"(syntax)|(segfault)|(core dumped)",
                       re.IGNORECASE)
    res = None
    with open(stdout, 'r', encoding='utf-8', errors='replace') as in_f:
        for line in in_f:
            line = line.strip()
            if correct.match(line):
                assert res is None
                res = "correct"
            elif wrong.match(line):
                assert res is None
                res = "wrong"
            elif memout.search(line):
                assert res is None
                res = "memout"
            if error.search(line):
                res = "error"
    if res is None:
        with open(stderr, 'r', encoding='utf-8', errors='replace') as in_f:
            for line in in_f:
                line = line.strip()
                if memout.search(line):
                    res = "memout"
                    break
                if timeout.search(line):
                    res = "timeout"
                    break
                if error.search(line):
                    res = "error"
                    break
    if res is None:
        res = "none"
    if res in {"none", "error", "wrong"}:
        if label not in known_errors["ctav"]:
            print(f"Found CTAV {res.upper()} in {stdout}")
            res = "error"
        else:
            res = "unknown"
    return res


def check_divine(stdout, stderr, expected_res) -> str:
    assert os.path.isfile(stdout)
    assert os.path.isfile(stderr)
    assert stdout.endswith(f".{tool2ext['divine']}.stdout")
    assert stderr.endswith(f".{tool2ext['divine']}.stderr")
    label = os.path.basename(stdout)[:-len(f".{tool2ext['divine']}.stdout")]
    if expected_res is True:
        wrong = re.compile(r"\s*The\s+property\s+DOES\s+NOT\s+hold")
        correct = re.compile(r"\s*The\s+property\s+HOLDS")
    else:
        correct = re.compile(r"\s*The\s+property\s+DOES\s+NOT\s+hold")
        wrong = re.compile(r"\s*The\s+property\s+HOLDS")
    memout = re.compile(r".*(Cannot\s+allocate\s+memory)|(std::bad_alloc)")
    unknown = re.compile(r"Segmentation fault", re.IGNORECASE)
    error = re.compile(r"(exception)|(TIMEOUT)|(\s+error)|(parse)", re.IGNORECASE)
    res = None
    with open(stderr, 'r', encoding='utf-8', errors='replace') as in_f:
        for line in in_f:
            line = line.strip()
            if correct.match(line):
                assert res is None
                res = "correct"
                break
            elif wrong.match(line):
                assert res is None
                res = "wrong"
                break
            elif memout.match(line):
                assert res is None or res in {"error", "memout"}
                res = "memout"
            elif unknown.search(line):
                res = "unknown"
            elif error.search(line) and res != "memout":
                res = "error"
    if res is None:
        res = "none"
    if res in {"none", "error", "wrong"}:
        if label not in known_errors["divine"]:
            print(f"Found DIVINE {res.upper()} in {stderr}")
            res = "error"
        else:
            res = "unknown"

    return res


def check_irankfinder(stdout, stderr, expected_res) -> str:
    assert os.path.isfile(stdout)
    assert os.path.isfile(stderr)
    assert stdout.endswith(f".{tool2ext['irankfinder']}.stdout")
    assert stderr.endswith(f".{tool2ext['irankfinder']}.stderr")
    assert expected_res is False
    label = os.path.basename(stdout)[:-len(f".{tool2ext['irankfinder']}.stdout")]
    correct = re.compile(r"NO")
    wrong = re.compile(r"YES")
    unknown = re.compile(r"MAYBE")
    memout = re.compile(r"memout", re.IGNORECASE)
    timeout = re.compile(r"KeyboardInterrupt")
    error = re.compile(r"(exception)|(TIMEOUT)", re.IGNORECASE)
    res = None
    with open(stdout, 'r', encoding='utf-8', errors='replace') as in_f:
        for line in in_f:
            line = line.strip()
            if correct.match(line):
                assert res is None or res == "correct"
                res = "correct"
            elif wrong.match(line):
                assert res is None
                res = "wrong"
            elif unknown.match(line):
                assert res is None
                res = "unknown"
            elif memout.search(line):
                res = "memout"
            if error.search(line):
                res = "error"
    if res is None:
        with open(stderr, 'r', encoding='utf-8', errors='replace') as in_f:
            for line in in_f:
                line = line.strip()
                if memout.search(line):
                    res = "memout"
                elif timeout.search(line):
                    res = "timeout"
                elif error.search(line):
                    res = "error"
                if res is not None:
                    break
    if res is None:
        res = "none"
    if res in {"none", "error", "wrong"}:
        if label not in known_errors["irankfinder"]:
            print(f"Found irankfinder {res.upper()} in {stdout}")
            res = "error"
        else:
            res = "unknown"
    return res


def check_ltsmin(stdout, stderr, expected_res) -> str:
    assert os.path.isfile(stdout)
    assert os.path.isfile(stderr)
    assert stdout.endswith(f".{tool2ext['ltsmin']}.stdout")
    assert stderr.endswith(f".{tool2ext['ltsmin']}.stderr")
    label = os.path.basename(stdout)[:-len(f".{tool2ext['ltsmin']}.stdout")]
    if expected_res:
        wrong = re.compile(r"Accepting cycle FOUND at depth \d+!")
        correct = re.compile(r"State space has \d+ states, 0 are accepting")
    else:
        correct = re.compile(r"Accepting cycle FOUND at depth \d+!")
        wrong = re.compile(r"State space has \d+ states, 0 are accepting")
    error = re.compile(r"(\s+error\s+)|(cannot open)|(syntax)|(segfault)|(SEGFAULT)",
                       re.IGNORECASE)
    memout = re.compile(r"buffer overflow")
    completed = re.compile(r"LTSMIN DONE")
    res = None
    with open(stdout, 'r', encoding='utf-8', errors='replace') as in_f:
        for line in in_f:
            line = line.strip()
            if completed.match(line):
                has_finish = True
            if error.search(line):
                res = "error"
    if res is None:
        with open(stderr, 'r', encoding='utf-8', errors='replace') as in_f:
            for line in in_f:
                line = line.strip()
                if correct.search(line):
                    assert res is None
                    res = "correct"
                elif wrong.search(line):
                    assert res is None
                    res = "wrong"
                if memout.search(line):
                    res = "memout"
                if error.search(line):
                    res = "error"
    if res is None:
        res = "none"
    if res in {"none", "error", "wrong"}:
        if label not in known_errors["ltsmin"]:
            print(f"Found LTSmin {res.upper()} in {stderr}")
            res = "error"
        else:
            res = "unknown"
    return res


def check_nuxmv(stdout, stderr, expected_res, name="nuxmv") -> str:
    assert os.path.isfile(stdout)
    assert os.path.isfile(stderr)
    tool_ext = tool2ext[name]
    assert stdout.endswith(f".{tool_ext}.stdout")
    assert stderr.endswith(f".{tool_ext}.stderr")
    label = os.path.basename(stdout)[:-len(f".{tool_ext}.stdout")]
    if expected_res is True:
        wrong = re.compile(r"-- (((LTL )?specification)|(invariant))\s+.*\s+is\s+false")
        correct = re.compile(r"-- (((LTL )?specification)|(invariant))\s+.*\s+is\s+true")
    else:
        correct = re.compile(r"-- (((LTL )?specification)|(invariant))\s+.*\s+is\s+false")
        wrong = re.compile(r"-- (((LTL )?specification)|(invariant))\s+.*\s+is\s+true")
    memout = re.compile(r"(Out of memory)|(bad_alloc)", re.IGNORECASE)
    error = re.compile(r"(ERROR)|(cannot open)|(must be built)")
    res = None
    with open(stdout, 'r', encoding='utf-8', errors='replace') as in_f:
        for line in in_f:
            line = line.strip()
            if correct.match(line):
                assert res is None
                res = "correct"
            elif wrong.match(line):
                assert res is None
                res = "wrong"
            if error.search(line):
                res = "error"
    if res is None:
        with open(stderr, 'r', encoding='utf-8', errors='replace') as in_f:
            for line in in_f:
                line = line.strip()
                if memout.search(line):
                    res = "memout"
                if res is not None:
                    break
    if res is None:
        res = "none"
    if res in {"none", "error", "wrong"}:
        if label not in known_errors[name]:
            print(f"Found {name} {res.upper()} in {stdout}")
            res = "error"
        else:
            res = "unknown"

    return res


def check_nuxmvbmc(stdout, stderr, expected_res) -> str:
    return check_nuxmv(stdout, stderr, expected_res, name="bmcnuxmv")


def check_f3(stdout, stderr, expected_res) -> str:
    assert os.path.isfile(stdout)
    assert os.path.isfile(stderr)
    assert stdout.endswith(f".{tool2ext['f3']}.stdout")
    assert stderr.endswith(f".{tool2ext['f3']}.stderr")
    assert expected_res is False
    label = os.path.basename(stdout)[:-len(f".{tool2ext['f3']}.stdout")]
    correct = re.compile(r"end\s+of\s+`.*`\s*:\s*SUCCESS")
    wrong = re.compile(r"end\s+of\s+`.*`\s*:\s*FAILURE")
    unknown = re.compile(r"end\s+of\s+`.*`\s*:\s*UNKNOWN")
    memout = re.compile(r"std::bad_alloc")
    error = re.compile(r"(error)|(exception)|(attributeerror)",
                       re.IGNORECASE)
    segfault = re.compile(r"segmentation", re.IGNORECASE)
    res = None
    with open(stdout, 'r', encoding='utf-8', errors='replace') as in_f:
        for line in in_f:
            line = line.strip()
            if correct.match(line):
                assert res is None
                res = "correct"
            elif wrong.match(line):
                assert res is None
                res = "wrong"
            elif unknown.match(line):
                assert res is None
                res = "unknown"
            if error.search(line):
                res = "error"
    if res is None:
        with open(stderr, 'r', encoding='utf-8', errors='replace') as in_f:
            for line in in_f:
                line = line.strip()
                if segfault.search(line):
                    res = "segfault"
                if memout.search(line):
                    res = "memout"
                if error.search(line):
                    res = "error"
    if res is None:
        res = "none"
    if res in {"none", "segfault", "memout", "error", "wrong"}:
        if label not in known_errors["f3"]:
            print(f"Found F3 {res.upper()} in {stdout}")
            res = "error"
        else:
            res = "unknown"
    return res


def check_t2(stdout, stderr, expected_res) -> str:
    assert os.path.isfile(stdout)
    assert os.path.isfile(stderr)
    assert stdout.endswith(f".{tool2ext['t2']}.stdout")
    assert stderr.endswith(f".{tool2ext['t2']}.stderr")
    assert expected_res is False
    label = os.path.basename(stdout)[:-len(f".{tool2ext['t2']}.stdout")]
    correct = re.compile(r"(Nontermination\s+proof\s+succeeded)|(Temporal\s+proof\s+failed)")
    wrong = re.compile(r"(Termination\s+proof\s+succeeded)|(Temporal\s+proof\s+succeeded)")
    unknown = re.compile(r"Termination/nontermination\s+proof\s+failed")
    error = re.compile(r"(error)|(exception)|(assert)", re.IGNORECASE)
    res = None
    with open(stdout, 'r', encoding='utf-8', errors='replace') as in_f:
        for line in in_f:
            line = line.strip()
            if correct.match(line):
                assert res is None
                res = "correct"
            elif wrong.match(line):
                assert res is None
                res = "wrong"
            elif unknown.match(line):
                assert res is None
                res = "unknown"
            if error.search(line):
                res = "error"
    if res is None:
        res = "none"
    if res in {"none", "error", "wrong"}:
        if label not in known_errors["t2"]:
            print(f"Found t2 {res.upper()} in {stdout}")
            res = "error"
        else:
            res = "unknown"
    return res


def check_ultimate_term(stdout, stderr, expected_res) -> str:
    assert stdout.endswith(f".{tool2ext['ultimate_term']}.stdout")
    assert stderr.endswith(f".{tool2ext['ultimate_term']}.stderr")
    label = os.path.basename(stdout)[:-len(f".{tool2ext['ultimate_term']}.stdout")]
    res = check_ultimate(stdout, stderr, expected_res)
    if res in {"none", "error", "wrong"}:
        if label not in known_errors["ultimate_term"]:
            print(f"Found Ultimate-term {res.upper()} in {stdout}")
            res = "error"
        else:
            res = "unknown"
    return res


def check_ultimate_ltl(stdout, stderr, expected_res) -> str:
    assert stdout.endswith(f".{tool2ext['ultimate_ltl']}.stdout")
    assert stderr.endswith(f".{tool2ext['ultimate_ltl']}.stderr")
    label = os.path.basename(stdout)[:-len(f".{tool2ext['ultimate_ltl']}.stdout")]
    res = check_ultimate(stdout, stderr, expected_res)
    if res in {"none", "error", "wrong"}:
        if label not in known_errors["ultimate_ltl"]:
            print(f"Found Ultimate-LTL {res.upper()} in {stdout}")
            res = "error"
        else:
            res = "unknown"
    return res


def check_ultimate(stdout, stderr, expected_res) -> str:
    assert os.path.isfile(stdout)
    assert os.path.isfile(stderr)
    if expected_res is True:
        wrong = re.compile(r"(RESULT: Ultimate proved your program to be incorrect!)|(.*execution that violates the LTL property)")
        correct = re.compile(r"(RESULT: Ultimate proved your program to be correct!)|(.*the\s+LTL\s+property.*holds)")
    else:
        correct = re.compile(r"(RESULT: Ultimate proved your program to be incorrect!)|(.*execution that violates the LTL property)")
        wrong = re.compile(r"(RESULT: Ultimate proved your program to be correct!)|(.*the\s+LTL\s+property.*holds)")
    unknown = re.compile(r"(Buchi Automizer is unable to decide)|(Ultimate could not prove your program:)")
    memout = re.compile(r"OutOfMemoryError")
    timeout = re.compile(r"Received shutdown request")
    error = re.compile(r"Syntax error")
    res = None
    with open(stdout, 'r', encoding='utf-8', errors='replace') as in_f:
        for line in in_f:
            line = line.strip()
            if correct.match(line):
                # assert res is None or res == "correct", (res, stdout)
                res = "correct"
            elif wrong.match(line):
                assert res in {None, "wrong"}, res
                res = "wrong"
            elif unknown.search(line):
                # assert res is None, (res, stdout)
                res = "unknown"
            elif memout.search(line):
                res = "memout"
            if res is None and error.search(line):
                res = "error"
            if res is None and timeout.search(line):
                res = "timeout"
    if res is None:
        res = "none"
    return res


def check_uppaal(stdout, stderr, expected_res) -> str:
    assert os.path.isfile(stdout)
    assert os.path.isfile(stderr)
    assert stdout.endswith(f".{tool2ext['uppaal']}.stdout")
    assert stderr.endswith(f".{tool2ext['uppaal']}.stderr")
    label = os.path.basename(stdout)[:-len(f".{tool2ext['uppaal']}.stdout")]
    if expected_res is True:
        wrong = re.compile(r".*Formula is NOT satisfied")
        correct = re.compile(r".*Formula is satisfied")
    else:
        correct = re.compile(r".*Formula is NOT satisfied")
        wrong = re.compile(r".*Formula is satisfied")
    error = re.compile(r"(syntax error)|(undefined)", re.IGNORECASE)
    res = None
    with open(stdout, 'r', encoding='utf-8', errors='replace') as in_f:
        for line in in_f:
            line = line.strip()
            if correct.match(line):
                # assert res is None or res == "correct", (res, stdout)
                res = "correct"
            elif wrong.match(line):
                assert res is None, res
                res = "wrong"
            if res is None and error.search(line):
                res = "error"
    if res is None:
        res = "none"
    if res in {"none", "error", "wrong"}:
        if label not in known_errors["uppaal"]:
            print(f"Found Uppaal {res.upper()} in {stdout}")
            res = "error"
        else:
            res = "unknown"

    return res


tool2check_f = {
    "anant": check_anant,
    "aprove": check_aprove,
    "atmoc": check_atmoc,
    "ctav": check_ctav,
    "divine": check_divine,
    "irankfinder": check_irankfinder,
    "ltsmin": check_ltsmin,
    # "mitlbmc": check_mitlbmc,
    "nuxmvbmc": check_nuxmv,
    "nuxmv": check_nuxmv,
    "f3": check_f3,
    "oldf3": check_f3,
    "t2": check_t2,
    "ultimate_term": check_ultimate_term,
    "ultimate_ltl": check_ultimate_ltl,
    "uppaal": check_uppaal
}


def parse_results(base_dir, tool_name, config: Config):
    global TO

    tool_name = tool_name.lower()
    check_result = tool2check_f[tool_name]
    tool_ext = tool2ext[tool_name]
    results = {}
    for _d0 in sorted(os.listdir(base_dir)):
        assert _d0 in Config.all_dirs, (_d0, Config.all_dirs)
        if config.is_dir2read(_d0) is False:
            continue
        expected_res = config.expected_res(_d0)
        d0 = os.path.join(base_dir, _d0)
        if os.path.isdir(d0):
            for _d1 in sorted(os.listdir(d0)):
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
                        data = parse_resources(stderr)
                        if not data.is_complete():
                            data = Resources()
                            data.wc_time, data.usr_time, data.sys_time = get_exec_time(stats)
                        total_time = sum(val if val else 0
                                         for val in [data.usr_time, data.sys_time])
                        tot_mem = sum(val if val is not None else 0
                                      for val in [data.maxrss, data.ixrss, data.idrss])
                        if total_time >= TO:
                            # assert res != "correct"
                            res = "timeout"
                        elif tot_mem >= MEM_LIM:
                            res = "memout"
                        else:
                            res = check_result(stdout, stderr, expected_res)
                        assert res in {"error", "timeout", "correct",
                                       "unknown", "memout"}
                        assert data.retval is None or res != "correct" or \
                            data.retval == 0
                        if res == "error":
                            assert label not in known_errors[tool_name]
                            res = "unknown"
                        curr[label] = (res, data)
    return results
