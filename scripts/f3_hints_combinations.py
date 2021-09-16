#! /usr/bin/env python3
# -*- coding: utf-8 -*-

import os
import argparse
from itertools import combinations
from random import shuffle, randint


def sample_iter(lst, k) -> list:
    it = iter(lst)
    # fill with first `k` elements
    res = []
    try:
        for _ in range(k):
            res.append(next(it))

        # randomise order.
        shuffle(res)
        # replace random items with decreasing probability.
        for i, v in enumerate(it, k):
            r = randint(0, i)
            if r < k:
                res[r] = v
    except StopIteration:
        pass
    return res


def main(bench_class: str, out_dir: str, max_combs: int):
    assert isinstance(bench_class, str)
    assert bench_class in {"ls", "ns", "its", "tts"}
    assert os.path.isdir(out_dir)
    assert isinstance(max_combs, int)
    assert max_combs > 0
    if bench_class == "ls":
        from ls_model_hints import bench_template, hints, label
    elif bench_class == "ns":
        from ns_model_hints import bench_template, hints, label
    elif bench_class == "its":
        from its_model_hints import bench_template, hints, label
    elif bench_class == "tts":
        from tts_model_hints import bench_template, hints, label

    assert isinstance(bench_template, str)
    assert isinstance(hints, list)
    assert isinstance(label, str)

    n_files = 0
    for n_pick in range(1, len(hints) + 1):
        for i, chosen_hints in enumerate(sample_iter(combinations(hints,
                                                                  n_pick),
                                                     max_combs)):
            assert len(chosen_hints) == n_pick
            out_f_name = f"{n_pick}-{label}_{i}.py"
            with open(os.path.join(out_dir, out_f_name), 'w') as out:
                out.write(bench_template.format("\n".join(chosen_hints)))
                n_files += 1
        print(f"Created {i+1} instances with {n_pick} hints")


def getopts():
    p = argparse.ArgumentParser()
    p.add_argument("-o", "--output", type=str,
                   help="output directory")
    p.add_argument("-t", "--type", type=str,
                   choices=["ls", "ns", "its", "tts"],
                   help="class of benchmarks for which to generate "
                   "wrong hints combinations")
    p.add_argument("-max", "--max-combinations", type=int,
                   default=20,
                   help="max number of combinations for each number of hints")
    return p.parse_args()


if __name__ == "__main__":
    opts = getopts()
    main(opts.type, opts.output, opts.max_combinations)
