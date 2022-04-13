#! /usr/bin/env python3

import os
import argparse
import re
from collections import defaultdict

from matplotlib import rcParams
from matplotlib import pyplot as plt
from matplotlib.lines import Line2D
from matplotlib.ticker import MaxNLocator, ScalarFormatter, LinearLocator
import tikzplotlib

from parse_results import parse_results, TO, Resources
from config import Config

rcParams.update({
    "pgf.texsystem": "pdflatex",
    "mathtext.fontset": "cm",
    "text.usetex": True,
    # "pgf.rcfonts": False,
    "font.family": "serif",
    "font.serif": [],
    "font.sans-serif": [],
    "savefig.bbox": "tight",
    "savefig.pad_inches": 0.05
})


tool2name = {"anant": "Anant",
             "atmoc": "ATMOC",
             "aprove": "AProVE",
             "ctav": "CTAV",
             "divine": "DIVINE",
             "irankfinder": "iRankFinder",
             "ltsmin": "LTSmin",
             # "mitlbmc": "ATMOC",
             "nuxmv": "nuXmv-IC3",
             "nuxmvbmc": "nuXmv-BMC",
             "f3": "F3",
             # "oldf3": "OldF3",
             "t2": "T2",
             "ultimate_term": "ULTIMATE-Term",
             "ultimate_ltl": "ULTIMATE-LTL",
             "uppaal": "Uppaal"}

tool2texname = {"anant": r"\textsc{Anant}",
                "atmoc": r"\textsc{ATMOC}",
                "aprove": r"\textsc{AProVe}",
                "ctav": r"\textsc{CTAV}",
                "divine": r"\textsc{DiVinE3}",
                "irankfinder": r"\textsc{iRankFinder}",
                "ltsmin": r"\textsc{LTSmin}",
                # "mitlbmc": "ATMOC",
                "nuxmv": r"\textsc{nuXmv-IC3}",
                "nuxmvbmc": r"\textsc{nuXmv-BMC}",
                "f3": r"\textsc{F3}",
                # "oldf3": "OldF3",
                "t2": r"\textsc{T2}",
                "ultimate_term": r"\textsc{Ultimate-Term}",
                "ultimate_ltl": r"\textsc{Ultimate-LTL}",
                "uppaal": r"\textsc{Uppaal}"}

tool2color = {"anant": "goldenrod",
              "aprove": "orange",
              "irankfinder": "deepskyblue",
              "t2": "deeppink",
              "ultimate_term": "purple",
              "ultimate_ltl": "dodgerblue",
              "atmoc": "darkorange",
              "ctav": "purple",
              "divine": "goldenrod",
              "ltsmin": "chocolate",
              "uppaal": "dodgerblue",
              "nuxmv": "c",
              "nuxmvbmc": "r",
              "f3": "lime",
              "best": "silver"}

tool2marker = {"anant": 'P',
               "aprove": 'X',
               "irankfinder": '>',
               "t2": '<',
               "ultimate_term": '^',
               "ultimate_ltl": 'v',
               "atmoc": 'P',
               "ctav": '^',
               "divine": 'v',
               "ltsmin": '<',
               "uppaal": '>',
               "nuxmv": 'X',
               "nuxmvbmc": "o",
               "f3": "*",
               "best": "s"}


def resource2time(in_data):
    assert isinstance(in_data, Resources)
    assert in_data.usr_time is not None
    assert in_data.sys_time is not None
    assert in_data.wc_time is not None
    return max(in_data.wc_time, in_data.usr_time + in_data.sys_time)


def group_results(data, bench_names, resource2value):
    tool_results = {}
    benchmarks = set()
    tools = list(sorted(data.keys()))
    for t_name in tools:
        stack = []
        for bench_name in bench_names:
            if bench_name in data[t_name].keys():
                stack.append(data[t_name][bench_name])
            else:
                print(f"Tool: {t_name}, benchname: {bench_name} not in data")
        name_to_res = {}
        while stack:
            curr = stack.pop()
            assert isinstance(curr, dict)
            assert all(isinstance(v, (dict, tuple)) for v in curr.values())
            for k, v in curr.items():
                if isinstance(v, dict):
                    stack.append(v)
                else:
                    assert isinstance(k, str)
                    assert k not in name_to_res, (k, t_name)
                    assert isinstance(v, tuple)
                    assert len(v) == 2
                    assert v[0] in {"timeout", "correct", "unknown", "memout"}
                    assert isinstance(v[1], Resources)
                    val = resource2value(v[1])
                    assert isinstance(val, (float, int))
                    assert v[0] != "correct" or val > 0, (t_name, k, val)
                    benchmarks.add(k)
                    name_to_res[k] = (v[0], val)
        tool_results[t_name] = name_to_res
    for t_name in tools:
        t_benchs = frozenset(tool_results[t_name].keys())
        assert benchmarks >= t_benchs
        for missing in list(benchmarks - t_benchs):
            tool_results[t_name][missing] = ("undef", 0.0)
    assert all(benchmarks == frozenset(tool_results[t_name].keys())
               for t_name in data)
    print(f"num instances: {len(benchmarks)}")
    t_correct = {}
    for t in sorted(tool_results.keys()):
        t_correct[t] = frozenset(b for b in benchmarks
                                 if tool_results[t][b][0] == "correct")
    for curr_t in sorted(t_correct.keys()):
        unique_solved = t_correct[curr_t]
        for other_t, other_solved in t_correct.items():
            if other_t != curr_t and (curr_t != "nuxmvbmc" or other_t != "nuxmv"):
                unique_solved -= other_solved
        print(f"{tool2name[curr_t]} solved: {len(t_correct[curr_t])}, "
              f"unique: {len(unique_solved)}")
    return tool_results, frozenset(benchmarks)


def plot_comparison(tool_results, benchmarks,
                    name=None,
                    title=None, legend=True,
                    x_label=True, y_label=True,
                    title_size=4, labels_size=12, marks_size=75,
                    line_width=1, ticks_size=12, legend_size=12):
    best_results = {b: ("unknown", TO) for b in benchmarks}

    for t_name, t_res in tool_results.items():
        for idx, b in enumerate(benchmarks):
            if t_res[b][0] == "correct":
                if best_results[b][0] != "correct":
                    best_results[b] = ("correct", t_res[b][1])
                else:
                    best_results[b] = ("correct", min(t_res[b][1],
                                                      best_results[b][1]))

    tools = ["best"]
    tools.extend(sorted(tool_results.keys()))
    tool_results["best"] = best_results
    _legend = []
    plt.figure(num=name,
               figsize=(6.30045, 3.6),
               dpi=500,
               linewidth=0.01,
               frameon=False,
               # tight_layout=True,
               constrained_layout=True,
    )
    ax = plt.gca()
    for x in ax.spines.values():
        x.set_linewidth(0.01)
    max_x_tick = 1
    for t_name in tools:
        t_res = tool_results[t_name]
        assert isinstance(t_name, str)
        t_res = list(sorted(t_res[b][1] for b in benchmarks
                            if t_res[b][0] == "correct"))
        acc = 0
        for idx, val in enumerate(t_res):
            acc += val
            t_res[idx] = acc
        assert all(isinstance(val, (int, float)) for val in t_res)
        if len(t_res) > 0:
            max_x_tick = max(len(t_res), max_x_tick)
            _legend.append(tool2texname[t_name]
                           if t_name != "best" else r"\textsc{Virt Best}")
            marker = tool2marker[t_name]
            unfilled = marker in frozenset(m for m, func in Line2D.markers.items()
                                           if func != 'nothing' and
                                           m not in Line2D.filled_markers)
            ax.scatter(# range(1, len(t_res) + 1), t_res,
                       t_res, range(1, len(t_res) + 1),
                       c=tool2color[t_name] if unfilled else None,
                       edgecolors=None if unfilled else tool2color[t_name],
                       facecolors=None if unfilled else "none",
                       s=marks_size if unfilled else marks_size / 3,
                       linewidths=line_width,
                       marker=marker, label=_legend[-1])

    if title:
        plt.title(title, fontsize=title_size)
    if legend:
        plt.legend(# loc="lower right",
                   loc="upper left",
                   # loc="best",
                   fontsize=legend_size, frameon=True,
                   ncol=2, scatteryoffsets=[0.5],
                   columnspacing=0.7, labelspacing=0.3,
                   borderpad=0.2, borderaxespad=0.3, handletextpad=0.05,
                   handlelength=1, handleheight=0.5)# .set_draggable(True)
    if x_label:
        plt.xlabel(# "solved benchmarks"
                   "time (s)", fontsize=labels_size)
    if y_label:
        plt.ylabel(# "time (s)"
                   "solved benchmarks", fontsize=labels_size)

    locator = MaxNLocator(nbins=10, steps=[1, 2, 4, 5, 10],
                          min_n_ticks=5,
                          integer=True)
    # ax.xaxis.set_major_locator(locator)
    ax.yaxis.set_major_locator(locator)

    # formatter = ScalarFormatter(useMathText=True, useOffset=False)
    # formatter.set_scientific(True)
    # formatter.set_powerlimits((-1, 2))
    # ax.yaxis.set_major_formatter(formatter)
    # ax.yaxis.get_offset_text().set_fontsize(labels_size)

    # ax.set_yscale('log')
    ax.set_xscale('log')
    offset = max(0.5, max_x_tick / 120)
    # ax.set_xlim(1-offset, max_x_tick + offset)
    # ax.set_ylim(0, max_x_tick + offset)
    plt.xticks(fontsize=ticks_size)
    plt.yticks(fontsize=ticks_size)
    # plt.grid(True, axis='y', which="both", linestyle=(0, (1, 5)))
    # ax.tick_params(axis='y', which="minor", length=0, width=0)
    plt.grid(True, axis='x', which="both", linestyle=(0, (3, 5)), alpha=0.5)
    ax.tick_params(axis='x', which="minor", length=0, width=0)
    # plt.subplots_adjust(top=0.998, bottom=0.102, right=0.995, left=0.088,
    #                     hspace=0, wspace=0)
    # plt.subplots_adjust(top=0.998, bottom=0.17, right=0.998, left=0.145,
    #                     hspace=0, wspace=0)
    # if name:
    #     tikzplotlib.clean_figure()
    #     tikzplotlib.save(f"/tmp/{name}.tex",
    #                      dpi=500,
    #                      strict=True,
    #                      axis_width="6.3in",
    #                      axis_height="3.5in")
    plt.savefig(f"/tmp/{name}.pgf", format="pgf", dpi=500)
    # plt.show(block=True)


def plot_scatter(tool_results, benchmarks,
                 title=None, legend=False,
                 show_x_timeout=False, show_y_timeout=False,
                 x_label=True, y_label=True,
                 title_size=12, labels_size=40, marks_size=400,
                 ticks_size=40, legend_size=20, line_width=3,
                 verbose=False):
    marker_colors = ['g', 'darkorange', 'm', 'r']
    marker_types = ['o', 'v', '<', 'P']
    # benchmarks = set()
    # tool_results = {}
    tools = list(sorted(frozenset(tool_results.keys()) - frozenset(["best"])))
    assert all(t in tool2name for t in tools), f"{tools} vs {tool2name.keys()}"
    x_tool = tools[0]
    if "f3" in tools:
        x_tool = "f3"
    elif "nuxmvbmc" in tools:
        x_tool = "nuxmvbmc"
    elif "nuxmv" in tools:
        x_tool = "nuxmv"

    benchmarks = sorted(benchmarks,
                        key=lambda test: tool_results[x_tool][test][1])
    # for t in sorted(tools):
    #     t_data = [tool_results[t][b] for b in benchmarks]
        # print(f"{tool2name[t]} solved: "
        #       f'{len(list(t_s for (t_t, t_s) in t_data if t_t == "correct"))}')
    # if "f3" in tools and "oldf3" in tools:
    #     f3_solved = frozenset(b for b in benchmarks
    #                           if tool_results["f3"][b][0] == "correct")
    #     oldf3_solved = frozenset(b for b in benchmarks
    #                              if tool_results["oldf3"][b][0] == "correct")
    #     if f3_solved == oldf3_solved:
    #         print("F3 and OldF3 solved the same problems")
    #     else:
    #         print(f"OldF3 additionally solved: {oldf3_solved - f3_solved}")
    #         print(f"F3 additionally solved: {f3_solved - oldf3_solved}")
    x_data = [tool_results[x_tool][b] for b in benchmarks]
    min_x = min(x for _, x in x_data)
    max_x = max(x for _, x in x_data)
    for y_tool in [t for t in tools if t != x_tool]:
        print("\n\nComparing "
              f"{tool2name[x_tool]} with {y_tool} on {len(benchmarks)} "
              "benchmarks\n")
        y_data = [tool_results[y_tool][b] for b in benchmarks]
        min_y = min(y for _, y in y_data)
        max_y = max(y for _, y in y_data)
        min_v = min(min_x, min_y) / 1.1
        if min_v <= 0:
            min_v = 0.01
        max_v = 1.1 * max(max_x, max_y)
        assert len(x_data) == len(y_data), y_tool
        corr_x = []
        corr_y = []
        undef_x_x = []
        undef_x_y = []
        undef_y_x = []
        undef_y_y = []
        undef_both_x = []
        undef_both_y = []
        undef_labels = frozenset({"undef", "timeout", "memout", "unknown"})
        for bench_label, (x_t, x_s), (y_t, y_s) in zip(benchmarks, x_data,
                                                       y_data):
            assert isinstance(x_t, str)
            assert isinstance(y_t, str)
            assert isinstance(x_s, (float, int))
            assert isinstance(y_s, (float, int))
            if verbose:
                print(f"< {bench_label} > "
                      f"{x_tool}: {x_t}, {x_s} <--> "
                      f"{y_tool}: {y_t}, {y_s}")
            if x_t == "correct" and y_t == "correct":
                assert x_s > 0
                assert y_s > 0
                corr_x.append(x_s)
                corr_y.append(y_s)
            elif x_t == "correct" and y_t in undef_labels:
                assert x_s > 0
                if y_s == 0:
                    y_s = min_v + 0.1
                undef_y_x.append(x_s)
                undef_y_y.append(y_s)
            elif y_t == "correct" and x_t in undef_labels:
                assert y_s > 0
                if x_s == 0:
                    x_s = min_v + 0.1
                undef_x_x.append(x_s)
                undef_x_y.append(y_s)
            elif y_t in undef_labels and x_t in undef_labels:
                if y_s == 0:
                    y_s = min_v + 0.1
                if x_s == 0:
                    x_s = min_v + 0.1
                undef_both_x.append(x_s)
                undef_both_y.append(y_s)
            else:
                raise Exception("Unhandled result: "
                                f"x_t: {x_t}; y_t: {y_t}")

        _legend = ["both answer", f"{tool2name['f3']} undef",
                   "{tool2name[y_tool]} undef",
                   "both undef"] if legend else [None]*4
        ax = plt.gca()
        for idx, (xs, ys) in enumerate([(corr_x, corr_y),
                                        (undef_x_x, undef_x_y),
                                        (undef_y_x, undef_y_y),
                                        (undef_both_x, undef_both_y)]):
            max_v = max(max_v, max(xs) if xs else max_v,
                        max(ys) if ys else max_v)
            min_v = min(min_v, min(xs) if xs else min_v,
                        min(ys) if ys else min_v)
            if xs:
                assert len(xs) == len(ys)
                assert isinstance(marker_colors[idx], str)
                assert isinstance(marker_types[idx], str)
                assert all(x <= max_v for x in xs)
                assert all(x >= min_v for x in xs)
                assert all(y <= max_v for y in ys)
                assert all(y >= min_v for y in ys)
                marker = marker_types[idx]
                unfilled = marker in \
                    frozenset(m for m, func in Line2D.markers.items()
                              if func != 'nothing' and
                              m not in Line2D.filled_markers)
                ax.scatter(xs, ys,
                           c=marker_colors[idx] if unfilled else None,
                           edgecolors=None if unfilled else marker_colors[idx],
                           facecolors=None if unfilled else "none",
                           marker=marker_types[idx],
                           linewidths=line_width,
                           s=marks_size if unfilled else marks_size / 3,
                           label=_legend[idx])

        if title:
            plt.title(title, fontsize=title_size)
        if legend:
            plt.legend(loc="best",
                       prop={'size': legend_size}).set_draggable(True)
        if x_label:
            plt.xlabel(f"{tool2name[x_tool]} (s)", fontsize=labels_size)
        if y_label:
            plt.ylabel(f"{tool2name[y_tool]} (s)", fontsize=labels_size)
        plt.xticks(fontsize=ticks_size)
        plt.yticks(fontsize=ticks_size)

        ax.plot((min_v, max_v), (min_v, max_v), color="gray",
                linewidth=line_width, linestyle='--', alpha=0.5)

        if show_y_timeout:
            x_bounds = plt.xlim()
            ax.plot((x_bounds[0], x_bounds[1]), (600, 600), color="red",
                    linewidth=line_width, linestyle='--', alpha=0.5)
            # ax.text(5, 200, "TO", size=20)
        if show_x_timeout:
            y_bounds = plt.ylim()
            ax.plot((600, 600), (y_bounds[0], y_bounds[1]), color="red",
                    linewidth=line_width, linestyle='--', alpha=0.5)
            # ax.text(5, 200, "TO", size=20)

        ax.set_yscale('log')
        ax.set_xscale('log')
        ax.set_aspect('equal', adjustable='box')
        plt.xlim([min_v, max_v])
        plt.ylim([min_v, max_v])
        plt.subplots_adjust(top=0.99, bottom=0.155, right=1, left=0,
                            hspace=0, wspace=0)
        plt.show(block=True)


def plot_scaling_hints(results, wrong_hints_benchs):
    t_name = "f3"
    assert all(bench in results[t_name] for bench in wrong_hints_benchs)
    name_re = re.compile(r"(?P<nhint>\d+)-(?P<name>\S+)_(?P<num>\d+)")
    for bench_class in sorted(wrong_hints_benchs):
        label = None
        wrong_hints = defaultdict(list)
        stack = [results[t_name][bench_class]]
        while stack:
            curr = stack.pop()
            assert isinstance(curr, dict)
            assert all(isinstance(v, (dict, tuple)) for v in curr.values())
            for k, v in curr.items():
                if isinstance(v, dict):
                    stack.append(v)
                else:
                    assert isinstance(k, str)
                    assert isinstance(v, tuple)
                    assert len(v) == 2
                    assert v[0] in {"timeout", "correct", "unknown",
                                    "memout"}, (t_name, v[0], k)
                    assert isinstance(v[1], float)
                    m = name_re.match(k)
                    assert m is not None
                    label = m.group("name")
                    assert label is None or label == m.group("name")
                    bench_size = int(m.group("nhint"))
                    wrong_hints[bench_size].append(v)
        assert label is not None
        f3_res = None
        # get time required without hints
        stack = [v for k, v in results[t_name].items()
                 if k not in wrong_hints_benchs]
        while stack:
            curr = stack.pop()
            assert isinstance(curr, dict)
            assert all(isinstance(v, (dict, tuple)) for v in curr.values())
            for k, v in curr.items():
                if isinstance(v, dict):
                    stack.append(v)
                elif k == label:
                    assert isinstance(k, str)
                    assert isinstance(v, tuple)
                    assert len(v) == 2
                    assert v[0] == "correct", (t_name, v[0], k)
                    assert isinstance(v[1], float)
                    assert f3_res is None
                    f3_res = v[1]
        assert f3_res is not None
        success_xs = [0]
        success_ys = [f3_res]
        failed_xs = []
        failed_ys = []
        sizes = sorted([int(x) for x in wrong_hints])
        for x in sizes:
            x = int(x)
            for y in wrong_hints[x]:
                if y[0] == "correct":
                    success_xs.append(x)
                    success_ys.append(y[1])
                else:
                    failed_xs.append(x)
                    failed_ys.append(y[1])
        print(f"Wrong hints `{label}`, "
              f"correct: {len(success_xs)}, failed: {len(failed_xs)}")
        labels_size = 45
        ticks_size = 45
        ax = plt.gca()
        min_x, max_x = min(success_xs), max(success_xs)
        min_y, max_y = min(success_ys), max(success_ys)
        if failed_xs:
            max_x = max(max_x, max(failed_xs))
            min_x = min(min_x, min(failed_xs))
        if failed_ys:
            max_y = max(max_y, max(failed_ys))
            min_y = min(min_y, min(failed_ys))

        ax.scatter(success_xs, success_ys, c='g', marker='o', s=400)
        ax.scatter(failed_xs, failed_ys, c='r', marker='P', s=400)
        ax.set_yscale('log')
        # ax.plot((0.5, 20.5), (1, 1), color="gray",
        #         linewidth=3, linestyle='--', alpha=0.5)
        plt.xlim([min_x - 0.5, max_x + 0.5])
        plt.ylim([min_y - 0.2, max_y + 0.2])
        plt.xlabel("Number of hints", fontsize=labels_size)
        plt.ylabel("F3 (s)", fontsize=labels_size)
        plt.yticks([10, 100, 1000])
        plt.subplots_adjust(top=0.995, bottom=0.126, right=0.995,
                            left=0.098,
                            hspace=0, wspace=0)
        ax.xaxis.set_major_locator(MaxNLocator(integer=True))
        plt.xticks(fontsize=ticks_size)
        plt.yticks(fontsize=ticks_size)
        plt.show(block=True)


def getopts():
    p = argparse.ArgumentParser()
    p.add_argument("-in", "--in-results", type=str,
                   required=True, help="results directory")
    p.add_argument("--scatter", action="store_true", default=False)
    p.add_argument("-ts", "--tools", type=str, nargs='+',
                   default=frozenset(tool2name.keys()),
                   help="consider only given tools")
    p.add_argument("-ls", "--linear-software", action="store_true",
                   help="plot results of linear software benchmarks")
    p.add_argument("-ns", "--nonlinear-software", action="store_true",
                   help="plot results of nonlinear software benchmarks")
    p.add_argument("-its", "--inf-state-ts", action="store_true",
                   help="plot results of infinite-state transition systems "
                   "benchmarks")
    p.add_argument("-maxp", "--max-plus", action="store_true",
                   help="plot results of max-plus benchmarks")

    p.add_argument("-tinv-ta", "--true-invar-timed-automata",
                   action="store_true",
                   help="plot results of true invar timed automata benchmarks")
    p.add_argument("-finv-ta", "--false-invar-timed-automata",
                   action="store_true",
                   help="plot results of false invar timed automata benchmarks")
    p.add_argument("-tltl-ta", "--true-ltl-timed-automata",
                   action="store_true",
                   help="plot results of true LTL timed automata benchmarks")
    p.add_argument("-fltl-ta", "--false-ltl-timed-automata",
                   action="store_true",
                   help="plot results of false LTL timed automata benchmarks")
    p.add_argument("-tmtl-ta", "--true-mtl-timed-automata",
                   action="store_true",
                   help="plot results of true MTL timed automata benchmarks")
    p.add_argument("-fmtl-ta", "--false-mtl-timed-automata",
                   action="store_true",
                   help="plot results of false MTL timed automata benchmarks")

    p.add_argument("-tts", "--timed-transition-systems", action="store_true",
                   help="plot results of timed transition systems benchmarks")
    p.add_argument("-hs", "--hybrid-systems", action="store_true",
                   help="plot results of hybrid systems benchmarks")
    p.add_argument("-hsh", "--hybrid-systems-hints", action="store_true",
                   help="plot results of hybrid systems hints benchmarks")
    p.add_argument("-c-hints", "--comb-hints", action="store_true",
                   help="plot results on F3 scaling w.r.t. combinations of "
                   "wrong hints")
    p.add_argument("-p-hints", "--perm-hints", action="store_true",
                   help="plot results on F3 scaling w.r.t. permutations of "
                   "wrong hints")
    p.add_argument("-v", "--verbose", action="store_true",
                   help="verbosly print single points")
    return p.parse_args()


def main(opts):
    in_dir = opts.in_results
    all_tools = frozenset(opts.tools)
    if not (frozenset(all_tools) <= frozenset(tool2name.keys())):
        missing = frozenset(all_tools) - frozenset(tool2name.keys())
        raise Exception(f"Unknown tools: `{missing}`")
    verbose = opts.verbose
    config = Config(opts)
    results = {}
    for t_name in sorted(all_tools):
        tool_dir = os.path.join(in_dir, f"{t_name}_results")
        if not os.path.isdir(tool_dir):
            raise Exception(f"Cannot find: `{tool_dir}`")
        print(f"Parsing {t_name} results.")
        results[t_name] = parse_results(tool_dir, t_name, config)
        if len(results[t_name]) == 0:
            raise Exception(f"No results for `{t_name}`")

    if config.nonterm_ls:
        print("\nLINEAR SOFTWARE TERMINATION")
        c_tools = all_tools & frozenset(["anant", "aprove", "irankfinder",
                                         "nuxmv", "nuxmvbmc", "f3", "t2",
                                         "ultimate_term"])
        res = {t_name: results[t_name] for t_name in c_tools}
        bench_names = ["software_nontermination"]
        res, benchs = group_results(res, bench_names, resource2time)
        plot_comparison(res, benchs, name="ls_comp")
        if opts.scatter:
            plot_scatter(res, benchs, verbose=verbose)

    if config.nonterm_ns:
        print("\nNON-LINEAR SOFTWARE TERMINATION")
        # ultimate does not support non-linear expressions.
        c_tools = all_tools & frozenset(["anant", "aprove", "irankfinder",
                                         "nuxmv", "nuxmvbmc", "f3", "t2"])
        res = {t_name: results[t_name] for t_name in c_tools}
        bench_names = ["nonlinear_software"]
        res, benchs = group_results(res, bench_names, resource2time)
        plot_comparison(res, benchs, name="ns_comp")
        if opts.scatter:
            plot_scatter(res, benchs, verbose=verbose)

    if config.fltl_maxp:
        print("\nMAX-PLUS")
        c_tools = all_tools & frozenset(["anant", "aprove", "irankfinder",
                                         "nuxmv", "nuxmvbmc", "f3", "t2",
                                         "ultimate_term"])
        res = {t_name: results[t_name] for t_name in c_tools}
        bench_names = ["maxplus"]
        res, benchs = group_results(res, bench_names, resource2time)
        plot_comparison(res, benchs, name="maxp_comp")
        if opts.scatter:
            plot_scatter(res, benchs, verbose=verbose)

    if config.fltl_its:
        print("\nLTL INFINITE STATE TRANSITION SYSTEMS")
        c_tools = all_tools & frozenset(["aprove", "irankfinder",
                                         "nuxmv", "nuxmvbmc", "f3",
                                         "ultimate_term", "ultimate_ltl"])
        res = {t_name: results[t_name] for t_name in c_tools}
        bench_names = ["airbag", "bakery_simple_bug", "bounded_counter",
                       "semaphore", "simple_int_loops", "simple_real_loops"]
        res, benchs = group_results(res, bench_names, resource2time)
        plot_comparison(res, benchs, name="its_comp")
        if opts.scatter:
            plot_scatter(res, benchs, verbose=verbose)

    # TIMED AUTOMATA
    if config.tinvar_ta:
        print("\nTRUE INVAR TIMED AUTOMATA")
        c_tools = all_tools & frozenset(["atmoc", "ctav", "divine",
                                         "ltsmin", "nuxmv", "uppaal"])
        res = {t_name: results[t_name] for t_name in c_tools}
        bench_names = ["ta_tinvar_critical_region", "ta_tinvar_csma",
                       "ta_tinvar_fddi", "ta_tinvar_fischer",
                       "ta_tinvar_lynch", "ta_tinvar_train"]
        res, benchs = group_results(res, bench_names, resource2time)
        plot_comparison(res, benchs, name="ta_tinv_comp")
        if opts.scatter:
            plot_scatter(res, benchs, verbose=verbose)

    if config.finvar_ta:
        print("\nFALSE INVAR TIMED AUTOMATA")
        c_tools = all_tools & frozenset(["atmoc", "ctav", "divine",
                                         "ltsmin", "nuxmv", "nuxmvbmc",
                                         "uppaal"])
        res = {t_name: results[t_name] for t_name in c_tools}
        bench_names = ["ta_finvar_critical_region", "ta_finvar_csma",
                       "ta_finvar_fddi", "ta_finvar_fischer",
                       "ta_finvar_lynch", "ta_finvar_train"]
        res, benchs = group_results(res, bench_names, resource2time)
        plot_comparison(res, benchs, name="ta_finv_comp")
        if opts.scatter:
            plot_scatter(res, benchs, verbose=verbose)

    if config.tltl_ta:
        print("\nTRUE LTL TIMED AUTOMATA")
        c_tools = all_tools & frozenset(["ctav", "divine", "ltsmin",
                                         "nuxmv", "uppaal"])
        res = {t_name: results[t_name] for t_name in c_tools}
        bench_names = ["ta_tltl_critical_region", "ta_tltl_csma",
                       "ta_tltl_fddi", "ta_tltl_fischer",
                       "ta_tltl_lynch", "ta_tltl_train"]
        res, benchs = group_results(res, bench_names, resource2time)
        plot_comparison(res, benchs, name="ta_tltl_comp")
        if opts.scatter:
            plot_scatter(res, benchs, verbose=verbose)

    if config.fltl_ta:
        print("\nFALSE LTL TIMED AUTOMATA")
        c_tools = all_tools & frozenset(["atmoc", "aprove", "ctav", "divine",
                                         "irankfinder", "ltsmin",
                                         "nuxmv", "nuxmvbmc", "f3",
                                         "ultimate_term", "ultimate_ltl",
                                         "uppaal"])
        res = {t_name: results[t_name] for t_name in c_tools}
        bench_names = ["ta_fltl_critical_region", "ta_fltl_csma",
                       "ta_fltl_fddi", "ta_fltl_fischer",
                       "ta_fltl_lynch", "ta_fltl_train"]
        res, benchs = group_results(res, bench_names, resource2time)
        plot_comparison(res, benchs, name="ta_fltl_comp")
        if opts.scatter:
            plot_scatter(res, benchs, verbose=verbose)

    if config.tmtl_ta:
        print("\nTRUE MTL TIMED AUTOMATA")
        c_tools = all_tools & frozenset(["ctav", "nuxmv"])
        res = {t_name: results[t_name] for t_name in c_tools}
        bench_names = ["ta_tmtl_critical_region", "ta_tmtl_csma",
                       "ta_tmtl_fddi", "ta_tmtl_fischer",
                       "ta_tmtl_lynch", "ta_tmtl_train"]
        res, benchs = group_results(res, bench_names, resource2time)
        plot_comparison(res, benchs, name="ta_tmtl_comp")
        if opts.scatter:
            plot_scatter(res, benchs, verbose=verbose)

    if config.fmtl_ta:
        print("\nFALSE MTL TIMED AUTOMATA")
        c_tools = all_tools & frozenset(["atmoc", "ctav", "nuxmv", "nuxmvbmc"])
        res = {t_name: results[t_name] for t_name in c_tools}
        bench_names = ["ta_fmtl_critical_region", "ta_fmtl_csma",
                       "ta_fmtl_fddi", "ta_fmtl_fischer",
                       "ta_fmtl_lynch", "ta_fmtl_train"]
        res, benchs = group_results(res, bench_names, resource2time)
        plot_comparison(res, benchs, name="ta_fmtl_comp")
        if opts.scatter:
            plot_scatter(res, benchs, verbose=verbose)

    if config.fltl_tts:
        print("\nLTL TIMED TRANSITION SYSTEMS")
        c_tools = all_tools & frozenset(["aprove", "irankfinder",
                                         "nuxmv", "nuxmvbmc", "f3",
                                         "ultimate_term", "ultimate_ltl"])
        res = {t_name: results[t_name] for t_name in c_tools}
        bench_names = ["tts_csma_backoff", "tts_dynamic_fischer",
                       "tts_dynamic_lynch", "tts_token_ring", "tts"]
        res, benchs = group_results(res, bench_names, resource2time)
        plot_comparison(res, benchs, name="tts_comp")
        if opts.scatter:
            plot_scatter(res, benchs, verbose=verbose)

    if config.fltl_hs:
        print("\nLTL HYBRID SYSTEMS")
        # ultimate does not support non-linear expressions.
        c_tools = all_tools & frozenset(["aprove", "irankfinder",
                                         "nuxmv", "nuxmvbmc", "f3"])
        res = {t_name: results[t_name] for t_name in c_tools}
        bench_names = ["hybrid_system"]
        res, benchs = group_results(res, bench_names, resource2time)
        plot_comparison(res, benchs, name="hs_comp")
        if opts.scatter:
            plot_scatter(res, benchs, verbose=verbose)

    if config.hint_combs:
        print("\nSCALING WRONG HINTS COMBINATIONS\n")
        benchs = frozenset([
            "wrong_hints_ltl_infinite_state",
            "wrong_hints_ltl_timed_transition_system",
            "wrong_hints_nonlinear_software", "wrong_hints_software"])
        plot_scaling_hints(results, benchs)

    if config.hint_perms:
        print("\nSCALING WRONG HINTS PERMUTATIONS\n")
        benchs = frozenset([
            "wrong_hints_permutations_ltl_infinite_state",
            "wrong_hints_permutations_ltl_timed_transition_system",
            "wrong_hints_permutations_nonlinear_software",
            "wrong_hints_permutations_software"])
        plot_scaling_hints(results, benchs)


if __name__ == "__main__":
    main(getopts())
