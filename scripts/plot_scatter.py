#! /usr/bin/env python3

import os
import argparse
import re
from collections import defaultdict
import matplotlib.pyplot as plt
from matplotlib.ticker import MaxNLocator

from parse_results import parse_results, TO
from config import Config


tool2name = {"anant": "Anant",
             "atmoc": "ATMOC",
             "aprove": "AProVE",
             "ctav": "CTAV",
             "divine": "DIVINE",
             "irankfinder": "iRankFinder",
             "ltsmin": "LTSmin",
             # "mitlbmc": "ATMOC",
             "nuxmv": "nuXmv",
             "nuxmvbmc": "nuXmv-BMC",
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
    if len(results) == 0:
        print(f"No results for {bench_names}")
        return
    marker_colors = ['g', 'darkorange', 'm', 'r']
    marker_types = ['o', 'v', '<', 'P']
    # collect benchmarks names
    benchmarks = set()
    tool_results = {}
    tools = list(sorted(results.keys()))
    x_tool = tools[0]
    if "f3" in tools:
        x_tool = "f3"
    elif "nuxmv" in tools:
        x_tool = "nuxmv"

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
                    assert v[0] in {"timeout", "correct", "unknown", "memout"}
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
        print(f"{tool2name[t]} solved: "
              f'{len(list(t_s for (t_t, t_s) in t_data if t_t == "correct"))}')
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
    for y_tool in [t for t in tools if t != x_tool]:
        print("\n\nComparing "
              f"{tool2name[x_tool]} with {y_tool} on {len(benchmarks)} "
              "benchmarks\n")
        y_data = [tool_results[y_tool][b] for b in benchmarks]
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
            assert isinstance(x_s, float)
            assert isinstance(y_s, float)
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
        plt.subplots_adjust(top=0.99, bottom=0.176, right=1, left=0,
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
    p.add_argument("-ts", "--tools", type=str, nargs='+',
                   default=frozenset(tool2name.keys()),
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
        print("\nLINEAR SOFTWARE TERMINATION\n")
        c_tools = all_tools & frozenset(["anant", "aprove", "irankfinder",
                                         "nuxmvbmc", "f3", "oldf3", "t2",
                                         "ultimate_term"])
        res = {t_name: results[t_name] for t_name in c_tools}
        plot_comparison(res, ["software_nontermination"], verbose=verbose)

    if config.nonterm_ns:
        print("\nNON-LINEAR SOFTWARE TERMINATION\n")
        # ultimate does not support non-linear expressions.
        c_tools = all_tools & frozenset(["anant", "aprove", "irankfinder",
                                         "nuxmvbmc", "f3", "oldf3", "t2"])
        res = {t_name: results[t_name] for t_name in c_tools}
        plot_comparison(res, ["nonlinear_software"], verbose=verbose)

    if config.fltl_maxp:
        print("\nMAX-PLUS\n")
        c_tools = all_tools & frozenset(["anant", "aprove", "irankfinder",
                                         "nuxmvbmc", "f3", "oldf3", "t2",
                                         "ultimate_term"])
        res = {t_name: results[t_name] for t_name in c_tools}
        plot_comparison(res, ["maxplus"], verbose=verbose)

    if config.fltl_its:
        print("\nLTL INFINITE STATE TRANSITION SYSTEMS\n")
        c_tools = all_tools & frozenset(["aprove", "irankfinder",
                                         "nuxmvbmc", "f3", "oldf3",
                                         "ultimate_term", "ultimate_ltl"])
        res = {t_name: results[t_name] for t_name in c_tools}
        plot_comparison(res, ["airbag", "bakery_simple_bug", "bounded_counter",
                              "semaphore", "simple_int_loops",
                              "simple_real_loops"],
                        verbose=verbose)

    # TIMED AUTOMATA
    if config.tinvar_ta:
        print("\nTRUE INVAR TIMED AUTOMATA\n")
        c_tools = all_tools & frozenset(["aprove", "atmoc", "ctav", "divine",
                                         "irankfinder", "ltsmin", "nuxmv",
                                         "ultimate_term", "ultimate_ltl",
                                         "uppaal"])
        res = {t_name: results[t_name] for t_name in c_tools}
        plot_comparison(res, ["ta_tinvar_critical_region", "ta_tinvar_csma_cd",
                              "ta_tinvar_fddi", "ta_tinvar_fischer",
                              "ta_tinvar_lynch", "ta_tinvar_train"],
                        verbose=verbose)

    if config.finvar_ta:
        print("\nFALSE INVAR TIMED AUTOMATA\n")
        c_tools = all_tools & frozenset(["aprove", "atmoc", "ctav", "divine",
                                         "irankfinder", "ltsmin",
                                         "nuxmv", "nuxmvbmc",
                                         "ultimate_term", "ultimate_ltl",
                                         "uppaal"])
        res = {t_name: results[t_name] for t_name in c_tools}
        plot_comparison(res, ["ta_finvar_critical_region", "ta_finvar_csma_cd",
                              "ta_finvar_fddi", "ta_finvar_fischer",
                              "ta_finvar_lynch", "ta_finvar_train"],
                        verbose=verbose)

    if config.tltl_ta:
        print("\nTRUE LTL TIMED AUTOMATA\n")
        c_tools = all_tools & frozenset(["aprove", "ctav", "divine",
                                         "irankfinder", "ltsmin", "nuxmv",
                                         "ultimate_term", "ultimate_ltl",
                                         "uppaal"])
        res = {t_name: results[t_name] for t_name in c_tools}
        plot_comparison(res, ["ta_tltl_critical_region", "ta_tltl_csma_cd",
                              "ta_tltl_fddi", "ta_tltl_fischer",
                              "ta_tltl_lynch", "ta_tltl_train"],
                        verbose=verbose)

    if config.fltl_ta:
        print("\nFALSE LTL TIMED AUTOMATA\n")
        c_tools = all_tools & frozenset(["atmoc", "aprove", "ctav", "divine",
                                         "irankfinder", "ltsmin",
                                         "nuxmv", "nuxmvbmc", "f3", "oldf3",
                                         "ultimate_term", "ultimate_ltl",
                                         "uppaal"])
        res = {t_name: results[t_name] for t_name in c_tools}
        plot_comparison(res, ["ta_fltl_critical_region", "ta_fltl_csma_cd",
                              "ta_fltl_fddi", "ta_fltl_fischer",
                              "ta_fltl_lynch", "ta_fltl_train"],
                        verbose=verbose)

    if config.tmtl_ta:
        print("\nTRUE MTL TIMED AUTOMATA\n")
        c_tools = all_tools & frozenset(["aprove", "ctav", "divine",
                                         "irankfinder", "ltsmin", "nuxmv",
                                         "ultimate_term", "ultimate_ltl",
                                         "uppaal"])
        res = {t_name: results[t_name] for t_name in c_tools}
        plot_comparison(res, ["ta_tmtl_critical_region", "ta_tmtl_csma_cd",
                              "ta_tmtl_fddi", "ta_tmtl_fischer",
                              "ta_tmtl_lynch", "ta_tmtl_train"],
                        verbose=verbose)

    if config.fmtl_ta:
        print("\nFALSE MTL TIMED AUTOMATA\n")
        c_tools = all_tools & frozenset(["aprove", "atmoc", "ctav", "divine",
                                         "irankfinder", "ltsmin",
                                         "nuxmv", "nuxmvbmc",
                                         "ultimate_term", "ultimate_ltl",
                                         "uppaal"])
        res = {t_name: results[t_name] for t_name in c_tools}
        plot_comparison(res, ["ta_fmtl_critical_region", "ta_fmtl_csma_cd",
                              "ta_fmtl_fddi", "ta_fmtl_fischer",
                              "ta_fmtl_lynch", "ta_fmtl_train"],
                        verbose=verbose)

    if config.fltl_tts:
        print("\nLTL TIMED TRANSITION SYSTEMS\n")
        c_tools = all_tools & frozenset(["aprove", "irankfinder", "nuxmvbmc",
                                         "f3", "oldf3", "ultimate_term",
                                         "ultimate_ltl"])
        res = {t_name: results[t_name] for t_name in c_tools}
        plot_comparison(res, ["tts_csma_backoff", "tts_dynamic_fischer",
                              "tts_dynamic_lynch", "tts_token_ring", "tts"],
                        verbose=verbose)

    if config.fltl_hs:
        print("\nLTL HYBRID SYSTEMS\n")
        # ultimate does not support non-linear expressions.
        c_tools = all_tools & frozenset(["aprove", "irankfinder", "nuxmvbmc",
                                         "f3", "oldf3"])
        res = {t_name: results[t_name] for t_name in c_tools}
        plot_comparison(res, ["hybrid_system"], verbose=verbose)

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
