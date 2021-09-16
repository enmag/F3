#! /usr/bin/env python3

import os
import argparse
import re
from math import sqrt
from collections import defaultdict
from parse_results import parse_results, TO
import matplotlib.pyplot as plt
from matplotlib.ticker import MaxNLocator


tool2name = {"anant": "Anant",
             "aprove": "AProVE",
             "divine": "DIVINE",
             "irankfinder": "iRankFinder",
             "mitlbmc": "MitlBMC",
             "nuxmv": "nuXmv",
             "f3": "F3",
             "oldf3": "OldF3",
             "t2": "T2",
             "ultimate_term": "ULTIMATE-Term",
             "ultimate_ltl": "ULTIMATE-LTL",
             "uppaal": "Uppaal"}


def plot_comparison(results, bench_names,
                    title=None, legend=False,
                    show_x_timeout=False, show_y_timeout=False,
                    x_label=True, y_label=True,
                    title_size=12, labels_size=60, marks_size=400,
                    ticks_size=60, legend_size=40, line_width=3,
                    verbose=False):
    marker_colors = ['g', 'darkorange', 'm', 'r']
    marker_types = ['o', 'v', '<', 'P']
    # collect benchmarks names
    benchmarks = set()
    tool_results = {}
    tools = list(sorted(results.keys()))
    x_tool = "f3" if "f3" in tools else tools[0]
    for t_name in tools:
        stack = []
        for bench_name in bench_names:
            if bench_name in results[t_name].keys():
                stack.append(results[t_name][bench_name])
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
                    assert v[0] in {"timeout", "correct", "unknown", "memout"}, (t_name, v[0], k)
                    assert isinstance(v[1], float)
                    benchmarks.add(k)
                    name_to_res[k] = v
        tool_results[t_name] = name_to_res
    benchmarks = frozenset(benchmarks)
    for t_name in tools:
        t_benchs = frozenset(tool_results[t_name].keys())
        assert benchmarks >= t_benchs
        for missing in list(benchmarks - t_benchs):
            tool_results[t_name][missing] = ("undef", 0.0)
    assert all(benchmarks == frozenset(tool_results[t_name].keys())
               for t_name in results)
    benchmarks = sorted(benchmarks,
                        key=lambda test: tool_results[x_tool][test][1])
    for t in sorted(tools):
        t_data = [tool_results[t][b] for b in benchmarks]
        print("{} solved: {}".format(tool2name[t],
                                     len(list(t_s for (t_t, t_s) in t_data
                                              if t_t == "correct"))))
    if "f3" in tools and "oldf3" in tools:
        f3_solved = frozenset(b for b in benchmarks
                              if tool_results["f3"][b][0] == "correct")
        oldf3_solved = frozenset(b for b in benchmarks
                                 if tool_results["oldf3"][b][0] == "correct")
        if f3_solved == oldf3_solved:
            print("F3 and OldF3 solved the same problems")
        else:
            print(f"OldF3 additionally solved: {oldf3_solved - f3_solved}")
            print(f"F3 additionally solved: {f3_solved - oldf3_solved}")
    x_data = [tool_results[x_tool][b] for b in benchmarks]
    min_v = 0.5
    max_v = 1.3 * TO
    for t in [t for t in tools if t != x_tool]:
        print(f"\n\nComparing {tool2name[x_tool]} with {t} on {len(benchmarks)} benchmarks\n")
        y_data = [tool_results[t][b] for b in benchmarks]
        assert len(x_data) == len(y_data), t
        corr_x = []
        corr_y = []
        undef_x_x = []
        undef_x_y = []
        undef_y_x = []
        undef_y_y = []
        undef_both_x = []
        undef_both_y = []
        undef_labels = frozenset({"undef", "timeout", "memout", "unknown"})
        for bench_label, (x_t, x_s), (y_t, y_s) in zip(benchmarks, x_data, y_data):
            assert isinstance(x_t, str)
            assert isinstance(y_t, str)
            assert isinstance(x_s, float)
            assert isinstance(y_s, float)
            if verbose:
                print(f"{bench_label} - {x_tool}: {x_t}, {x_s} - {t}: {y_t}, {y_s}")
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
                import pdb
                pdb.set_trace()
                print(f"x_t: {x_t}; y_t: {y_t}")

        _legend = ["both answer", f"{tool2name['f3']} undef",
                   "{tool2name[t]} undef",
                   "both undef"] if legend else [None]*4
        ax = plt.gca()

        for idx, (xs, ys) in enumerate([(corr_x, corr_y),
                                        (undef_x_x, undef_x_y),
                                        (undef_y_x, undef_y_y),
                                        (undef_both_x, undef_both_y)]):
            if xs:
                assert len(xs) == len(ys)
                assert isinstance(marker_colors[idx], str)
                assert isinstance(marker_types[idx], str)
                assert all(x <= max_v for x in xs)
                assert all(x >= min_v for x in xs)
                assert all(y <= max_v for y in ys)
                assert all(y >= min_v for y in ys)
                ax.scatter(xs, ys,
                           c=marker_colors[idx], marker=marker_types[idx],
                           s=marks_size,
                           label=_legend[idx])

        if title:
            plt.title(title, fontsize=title_size)
        if legend:
            plt.legend(loc="best", prop={'size': legend_size}).set_draggable(True)
        if x_label:
            plt.xlabel(f"{tool2name[x_tool]} (s)", fontsize=labels_size)
        if y_label:
            plt.ylabel(f"{tool2name[t]} (s)", fontsize=labels_size)
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
        plt.subplots_adjust(top=0.99, bottom=0.176, right=1, left=0,
                            hspace=0, wspace=0)
        plt.show(block=True)


def plot_scaling_hints(results, wrong_hints_benchs):
    t_name = "f3"
    assert all(bench in results[t_name] for bench in wrong_hints_benchs)
    name_re = re.compile("(?P<nhint>\d+)-(?P<name>\S+)_(?P<num>\d+)")
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
    p.add_argument("-ts", "--tools", type=str, nargs='+', default=None,
                   help="consider only given tools")
    p.add_argument("-in", "--in-results", type=str,
                   required=True,
                   help="results directory")
    p.add_argument("-ls", "--linear-software", action="store_true",
                   help="plot results of linear software benchmarks")
    p.add_argument("-ns", "--nonlinear-software", action="store_true",
                   help="plot results of nonlinear software benchmarks")
    p.add_argument("-its", "--inf-state-ts", action="store_true",
                   help="plot results of infinite-state transition systems "
                   "benchmarks")
    p.add_argument("-maxp", "--max-plus", action="store_true",
                   help="plot results of max-plus benchmarks")
    p.add_argument("-ta", "--timed-automata", action="store_true",
                   help="plot results of timed automata benchmarks")
    p.add_argument("-tts", "--timed-transition-systems", action="store_true",
                   help="plot results of timed transition systems benchmarks")
    p.add_argument("-hs", "--hybrid-systems", action="store_true",
                   help="plot results of hybrid systems benchmarks")
    p.add_argument("-c-hints", "--comb-hints", action="store_true",
                   help="plot results on F3 scaling w.r.t. combinations of wrong hints")
    p.add_argument("-p-hints", "--perm-hints", action="store_true",
                   help="plot results on F3 scaling w.r.t. permutations of wrong hints")
    p.add_argument("-v", "--verbose", action="store_true",
                   help="verbosly print single points")
    return p.parse_args()


def main(opts):
    in_dir = opts.in_results
    all_tools = opts.tools if opts.tools else list(tool2name.keys())
    verbose = opts.verbose
    results = {}
    _tools = set()
    for t_name in all_tools:
        tool_dir = os.path.join(in_dir, f"{t_name}_results")
        if not os.path.isdir(tool_dir):
            print(f"Cannot find: {tool_dir}")
        else:
            _tools.add(t_name)
            results[t_name] = parse_results(tool_dir, t_name)
    all_tools = frozenset(_tools)
    del _tools

    if opts.linear_software:
        print("\nLINEAR SOFTWARE TERMINATION\n")
        c_tools = all_tools & frozenset(["anant", "aprove", "irankfinder",
                                         "nuxmv", "f3", "oldf3", "t2", "ultimate_term"])
        res = {t_name: results[t_name] for t_name in c_tools}
        plot_comparison(res, ["software_nontermination"], verbose=verbose)

    if opts.nonlinear_software:
        print("\nNON-LINEAR SOFTWARE TERMINATION\n")
        # ultimate does not support non-linear expressions.
        c_tools = all_tools & frozenset(["anant", "aprove", "irankfinder",
                                         "nuxmv", "f3", "oldf3", "t2"])
        res = {t_name: results[t_name] for t_name in c_tools}
        plot_comparison(res, ["nonlinear_software"], verbose=verbose)

    if opts.max_plus:
        print("\nMAX-PLUS\n")
        c_tools = all_tools & frozenset(["anant", "aprove", "irankfinder",
                                         "nuxmv", "f3", "oldf3", "t2", "ultimate_term"])
        res = {t_name: results[t_name] for t_name in c_tools}
        plot_comparison(res, ["maxplus"], verbose=verbose)

    if opts.inf_state_ts:
        print("\nLTL INFINITE STATE TRANSITION SYSTEMS\n")
        c_tools = all_tools & frozenset(["aprove", "irankfinder",
                                         "nuxmv", "f3", "oldf3",
                                         "ultimate_term", "ultimate_ltl"])
        res = {t_name: results[t_name] for t_name in c_tools}
        plot_comparison(res, ["airbag", "bakery_simple_bug", "bounded_counter",
                              "semaphore", "simple_int_loops", "simple_real_loops"],
                        verbose=verbose)

    if opts.timed_automata:
        print("\nLTL TIMED AUTOMATA\n")
        c_tools = all_tools & frozenset(["aprove", "divine", "irankfinder",
                                         "mitlbmc", "nuxmv", "f3", "oldf3",
                                         "ultimate_term", "ultimate_ltl",
                                         "uppaal"])
        res = {t_name: results[t_name] for t_name in c_tools}
        plot_comparison(res, ["ta_critical_region", "ta_csma_cd", "ta_fddi",
                              "ta_fischer", "ta_lynch", "ta_train"],
                        verbose=verbose)

    if opts.timed_transition_systems:
        print("\nLTL TIMED TRANSITION SYSTEMS\n")
        c_tools = all_tools & frozenset(["aprove", "irankfinder", "nuxmv", "f3",
                                         "oldf3", "ultimate_term", "ultimate_ltl"])
        res = {t_name: results[t_name] for t_name in c_tools}
        plot_comparison(res, ["tts_csma_backoff", "tts_dynamic_fischer",
                              "tts_dynamic_lynch", "tts_token_ring", "tts"],
                        verbose=verbose)

    if opts.hybrid_systems:
        print("\nLTL HYBRID SYSTEMS\n")
        # ultimate does not support non-linear expressions.
        c_tools = all_tools & frozenset(["aprove", "irankfinder", "nuxmv", "f3",
                                         "oldf3"])
        res = {t_name: results[t_name] for t_name in c_tools}
        plot_comparison(res, ["hybrid_system"], verbose=verbose)

    if opts.comb_hints:
        print("\nSCALING WRONG HINTS COMBINATIONS\n")
        benchs = frozenset([
            "wrong_hints_ltl_infinite_state",
            "wrong_hints_ltl_timed_transition_system",
            "wrong_hints_nonlinear_software", "wrong_hints_software"])
        plot_scaling_hints(results, benchs)

    if opts.perm_hints:
        print("\nSCALING WRONG HINTS PERMUTATIONS\n")
        benchs = frozenset([
            "wrong_hints_permutations_ltl_infinite_state",
            "wrong_hints_permutations_ltl_timed_transition_system",
            "wrong_hints_permutations_nonlinear_software",
            "wrong_hints_permutations_software"])
        plot_scaling_hints(results, benchs)


if __name__ == "__main__":
    main(getopts())
