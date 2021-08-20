import csv
import os
import sys
import argparse
import pyparsing as pp

pp.ParserElement.enablePackrat()
sys.setrecursionlimit(3000)

C_ULT_TEMPLATE = """//@ ltl invariant negative: {ltl};

int main()
{{
{decl_vars}
  while(1) {{
{x_vars_assignments}
{step_assignments}
  }}
  return 0;
}}
"""


def read_matrix(mat_dir, n, no):
    fname = os.path.join(mat_dir, f"mat_{n}_{no}.txt")
    assert os.path.isfile(fname)
    res = []
    with open(fname, 'r') as fh:
        for line in fh:
            line = line.strip().split()
            assert len(line) == n
            res.append([float(x.strip()) if x.strip() != '-inf' else None
                        for x in line])
    assert len(res) == n
    return res


def parse_formula(formula):
    def rename(formula):
        S = [['!', 'not'], ['<->', 'iff'], ['->', 'implies'], ['|', 'or'], ['&', 'and']]
        for s in S:
            formula = formula.replace(s[0], s[1])
        return(formula)

    num = pp.pyparsing_common.fnumber.setParseAction(lambda toks: str(toks[0]))
    atom = pp.Word(pp.alphas, pp.alphanums + '_') + pp.Literal('-') + pp.Word(pp.alphas, pp.alphanums + '_') +  (pp.Literal('>=') | pp.Literal('>')) + num
    atom.setParseAction(lambda toks: ' '.join(toks))
    ltl_unary_ops = pp.Literal('F') | pp.Literal('G') | pp.Literal('X')
    ltl_binary_ops = pp.Literal('R') | pp.Literal('U')
    implies_ops = pp.Literal("implies") | pp.Literal("iff")
    or_ops = pp.Literal("or") | pp.Literal('xor')
    ltl_expr = pp.infixNotation(
        atom,
        [
            ("not", 1, pp.opAssoc.RIGHT),
            (ltl_unary_ops, 1, pp.opAssoc.RIGHT),
            ("and", 2, pp.opAssoc.LEFT),
            (implies_ops, 2, pp.opAssoc.LEFT),
            (or_ops, 2, pp.opAssoc.LEFT),
            (ltl_binary_ops, 2, pp.opAssoc.LEFT)
        ],
    )
    p = ltl_expr.parseString(rename(formula))
    return p[0]


def op(x):
    if x == "and":
        return "&&"
    if x == "or":
        return "||"
    if x == "not":
        return "!"
    if x == "G":
        return "[]"
    if x == "F":
        return "<>"
    if x == "implies":
        return "==>"
    if x == "iff":
        return "<==>"
    return x


def rewrite_formula(ltl):
    if isinstance(ltl, str):  # atom
        return f'({ltl})'
    if len(ltl) == 2:  # unary op
        return f"({op(ltl[0])} {rewrite_formula(ltl[1])})"

    lhs = ltl[0]
    if len(ltl) != 3:
        lhs = ltl[0:-2]

    return f"({rewrite_formula(lhs)} {op(ltl[-2])} {rewrite_formula(ltl[-1])})"


def encode_max(c):
    if len(c) == 1:
        return c[0]
    if len(c) == 2:
        lhs = c[0]
        rhs = c[1]
    else:
        pivot = len(c) // 2
        lhs = encode_max(c[0:pivot])
        rhs = encode_max(c[pivot:])

    return f"({lhs} > {rhs}? {lhs} : {rhs})"


def encode(matrix, ltl):
    decl_vars = []
    x_vars_assignments = []
    step_assignments = []
    for i, row in enumerate(matrix):
        vi = f"v{i}"
        x_vi = f"_x_{vi}"
        decl_vars.append(f"  float {vi}, {x_vi};")
        step_assignments.append(f"{vi} = {x_vi};")
        c = []
        for j, e in enumerate(row):
            if e is not None:
                c.append(f"({e} + v{j})")
        assert len(c) > 0
        x_vars_assignments.append(f"{x_vi} = {encode_max(c)};")

    return C_ULT_TEMPLATE.format(ltl=ltl,
                                 decl_vars="\n".join(decl_vars),
                                 x_vars_assignments="\n".join(x_vars_assignments),
                                 step_assignments="\n".join(step_assignments))


def main(ltl_file, data_file, in_dir, out_dir, keep):
    assert os.path.isfile(ltl_file)
    assert os.path.isfile(data_file)
    assert os.path.isdir(in_dir)
    assert os.path.isdir(out_dir)
    # WARNING: This assumes the two files are in the same order
    with open(ltl_file, 'r') as fh:
        reader = list(csv.DictReader(fh))
        for row in reader:
            # eigen = r2['eigenvalue'].split("/")
            n = int(row['dim'])
            no = int(row['no'])
            name = f"maxplus_{n}_{no}"
            if keep(name):
                matrix = read_matrix(in_dir, n, no)
                formula = row['formula']
                ltl = parse_formula(formula)
                ltl = rewrite_formula(ltl)
                ltl = ltl.replace('-x', ' - x')

                txt = encode(matrix, ltl)
                # txt = encode(matrix, ltl, int(eigen[0]), int(eigen[1]))
                with open(os.path.join(out_dir, f"{name}.c"), 'w') as out_f:
                    out_f.write(txt)


def getopts():
    p = argparse.ArgumentParser()
    p.add_argument("-ltl", "--ltl-formulae", type=str,
                   help="file containing LTL specifications")
    p.add_argument("-data", "--data-matrix", type=str,
                   help="file containing the data matrix")
    p.add_argument("-out", "--out-dir", type=str,
                   help="directory where to write encoded files")
    p.add_argument("-in", "--in-dir", type=str,
                   help="dictory containing the benchmarks with name `mat_*`")
    p.add_argument("-filter", "--filter", type=str, default=None,
                   help="consider only benchmarks whose name is contained "
                   "in the given file")
    return p.parse_args()


if __name__ == "__main__":
    opts = getopts()
    keep = lambda n: True
    if opts.filter is not None:
        assert os.path.isfile(opts.filter)
        keep_f = set()
        with open(opts.filter, 'r') as in_f:
            for line in in_f:
                line = line.strip().split()
                keep_f.update(l.strip() for l in line)
        keep_f = frozenset(keep_f)
        keep = lambda n: n in keep_f
    main(opts.ltl_formulae, opts.data_matrix, opts.in_dir,
         opts.out_dir, keep)
