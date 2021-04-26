#! /usr/bin/env python3

import os
import argparse
from parse_results import parse_results, TO
import matplotlib.pyplot as plt


tool2name = {"anant": "Anant",
             "aprove": "AProVE",
             "divine": "DIVINE",
             "mitlbmc": "MitlBMC",
             "nuxmv": "nuXmv",
             "f3": "F3",
             "t2": "T2",
             "ultimate": "ULTIMATE",
             "uppaal": "Uppaal"}

tool2markercolor = {
    "anant": "darkorange",
    "aprove": 'b',
    "divine": 'y',
    "mitlbmc": 'c',
    "nuxmv": 'r',
    "f3": 'g',
    "t2": 'm',
    "ultimate": 'b',
    "uppaal": 'magenta'
}

tool2markertype = {
    "anant": 'v',
    "aprove": '^',
    "divine": 'P',
    "mitlbmc": 'X',
    "nuxmv": 's',
    "f3": 'o',
    "t2": '<',
    "ultimate": 'd',
    "uppaal": "2"
}


def plot_comparison(results, bench_names,
                    title=None, legend=False,
                    show_x_timeout=False, show_y_timeout=False,
                    x_label=True, y_label=True,
                    title_size=12, labels_size=60, marks_size=400,
                    ticks_size=60, legend_size=40, line_width=3):
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
        print("{} solved: {}".format(tool2name[t],
                                     len(list(t_s for (t_t, t_s) in t_data
                                              if t_t == "correct"))))
    x_data = [tool_results[x_tool][b] for b in benchmarks]
    min_v = 0.5
    max_v = 1.3 * TO
    for t in [t for t in tools if t != x_tool]:
        print("\n\nComparing {} with {} on {} benchmarks\n"
              .format(tool2name[x_tool], t, len(benchmarks)))
        y_data = [tool_results[t][b] for b in benchmarks]
        if len(x_data) != len(y_data):
            import pdb
            pdb.set_trace()
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
            print("{} - {}: {}, {} - {}: {}, {}".format(bench_label, x_tool,
                                                        x_t, x_s, t, y_t, y_s))
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
                print("x_t: {}; y_t: {}".format(x_t, y_t))

        _legend = ["both answer", "{} undef".format(tool2name["f3"]),
                   "{} undef".format(tool2name[t]),
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
            plt.xlabel("{} (s)".format(tool2name[x_tool]), fontsize=labels_size)
        if y_label:
            plt.ylabel("{} (s)".format(tool2name[t]), fontsize=labels_size)
        plt.xticks(fontsize=ticks_size)
        plt.yticks(fontsize=ticks_size)

        ax.plot((min_v, max_v), (min_v, max_v), color="gray", linewidth=line_width,
                linestyle='--', alpha=0.5)

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


def getopts():
    p = argparse.ArgumentParser()
    p.add_argument("-ts", "--tools", type=str, nargs='+', default=None,
                   help="consider only given tools")
    p.add_argument("-in", "--in-results", type=str,
                   required=True,
                   help="results directory")
    p.add_argument("-software", "--software", action="store_true",
                   help="plot results of software benchmarks")
    p.add_argument("-inf-ts", "--inf-state-ts", action="store_true",
                   help="plot results of infinite-state transition systems "
                   "benchmarks")
    p.add_argument("-ta", "--timed-automata", action="store_true",
                   help="plot results of timed automata benchmarks")
    p.add_argument("-tts", "--timed-transition-systems", action="store_true",
                   help="plot results of timed transition systems benchmarks")
    p.add_argument("-hs", "--hybrid-systems", action="store_true",
                   help="plot results of hybrid systems benchmarks")
    return p.parse_args()


if __name__ == "__main__":
    title_size = 12
    labels_size = 60
    marks_size = 400
    ticks_size = 60
    legend_size = 40
    line_width = 3
    opts = getopts()
    in_dir = opts.in_results
    all_tools = opts.tools if opts.tools else list(tool2name.keys())
    results = {}
    _tools = set()
    for t_name in all_tools:
        tool_dir = os.path.join(in_dir, "{}_results".format(t_name))
        if not os.path.isdir(tool_dir):
            print("Cannot find: {}".format(tool_dir))
        else:
            _tools.add(t_name)
            results[t_name] = parse_results(tool_dir, t_name)
    all_tools = frozenset(_tools)
    del _tools

    if opts.software:
        print("\nLINEAR SOFTWARE TERMINATION\n")
        res = {"anant": results["anant"],
               "aprove": results["aprove"],
               "nuxmv": results["nuxmv"],
               "f3": results["f3"],
               "t2": results["t2"],
               "ultimate": results["ultimate"]}
        plot_comparison(res, ["software_nontermination"])

        print("\nNON-LINEAR SOFTWARE TERMINATION\n")
        # ultimate does not support non-linear expressions.
        res = {"anant": results["anant"],
               "aprove": results["aprove"],
               "nuxmv": results["nuxmv"],
               "f3": results["f3"],
               "t2": results["t2"]}
        plot_comparison(res, ["nonlinear_software"])

    if opts.inf_state_ts:
        print("\nLTL INFINITE STATE TRANSITION SYSTEMS\n")
        res = {"nuxmv": results["nuxmv"],
               "f3": results["f3"],
               "ultimate": results["ultimate"]}
        plot_comparison(res, ["airbag", "bakery_simple_bug", "bounded_counter",
                              "semaphore", "simple_int_loops", "simple_real_loops"])

    if opts.timed_automata:
        print("\nLTL TIMED AUTOMATA\n")
        res = {"divine": results["divine"],
               "mitlbmc": results["mitlbmc"],
               "nuxmv": results["nuxmv"],
               "f3": results["f3"],
               "ultimate": results["ultimate"],
               "uppaal": results["uppaal"]}
        plot_comparison(res, ["ta_critical_region", "ta_csma_cd", "ta_fddi",
                              "ta_fischer", "ta_lynch", "ta_train"])

    if opts.timed_transition_systems:
        print("\nLTL TIMED TRANSITION SYSTEMS\n")
        res = {"nuxmv": results["nuxmv"],
               "f3": results["f3"],
               "ultimate": results["ultimate"]}
        plot_comparison(res, ["tts_csma_backoff", "tts_dynamic_fischer",
                              "tts_dynamic_lynch", "tts_token_ring", "tts"])

    if opts.hybrid_systems:
        print("\nLTL HYBRID SYSTEMS\n")
        # ultimate does not support non-linear expressions.
        res = {"nuxmv": results["nuxmv"],
               "f3": results["f3"]}
        plot_comparison(res, ["hybrid_system"])
