#! /usr/bin/env python3
# -*- coding: utf-8 -*-

from typing import Optional
import os
import sys
import argparse
from itertools import chain
from importlib.util import spec_from_file_location, module_from_spec
path = os.path.abspath(os.path.join(os.path.dirname(os.path.realpath(__file__)),
                                    "../src"))
sys.path.append(path)

from pysmt.environment import pop_env, Environment as PysmtEnv

import mathsat

from solver import Solver
from encode_diverging import encode_diverging
from ltl.ltl import LTLEncoder, Options
from expr_utils import symb2next, symb2curr, symb_is_curr
from c_like_printer import to_c


c_template = """extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);
typedef enum {{false, true}} bool;
bool __VERIFIER_nondet_bool(void) {{
  return __VERIFIER_nondet_int() != 0;
}}

int main()
{{
{decl_symbs}
  int __steps_to_fair = __VERIFIER_nondet_int();
{curr_nondet}
  bool __ok = {init};
  while (__steps_to_fair >= 0 && __ok) {{
    if ({fair}) {{
      __steps_to_fair = __VERIFIER_nondet_int();
    }} else {{
      __steps_to_fair--;
    }}
{next_nondet}
    __ok = {trans};
{step_assign}
  }}
}}
"""


c_ltl_template = """//@ ltl invariant negative: {ultimate_ltl};
extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);
typedef enum {{false, true}} bool;
bool __VERIFIER_nondet_bool(void) {{
  return __VERIFIER_nondet_int() != 0;
}}

bool __ok;
{decl_symbs}
int main()
{{
{curr_nondet}
  __ok = {init};
  while (__ok) {{
{next_nondet}
    __ok = {trans};
{step_assign}
  }}
}}
"""


def translate(test_file: str, c_file: str,
              spec_file: Optional[str] = None):
    env = PysmtEnv()
    mgr = env.formula_manager
    # load test file.
    test_spec = spec_from_file_location("test", test_file)
    test_module = module_from_spec(test_spec)
    test_spec.loader.exec_module(test_module)
    assert not (hasattr(test_module, "transition_system") and
                hasattr(test_module, "check_ltl"))
    ltl = None
    ultimate_ltl = None
    if hasattr(test_module, "transition_system"):
        symbols, init, trans, fairness = test_module.transition_system(env)
        fairness = to_c(env, fairness)
        if spec_file is not None:
            ltl = f"(A F (G (! ({fairness}))))"
            ultimate_ltl = f"<> [] AP({fairness})"
    else:
        assert hasattr(test_module, "check_ltl")
        get_free_vars = env.fvo.get_free_variables
        with Solver(env=env, name="msat",
                    solver_options={'allow_bool_function_args': 'true'}) as solver:
            menv = solver.msat_env()
            convert = solver.converter.back
            opts = Options()
            opts.ltl_single_fairness_sorted = False
            enc = LTLEncoder(opts, menv)
            ok = enc.init()
            assert ok
            msat_symbs, msat_init, msat_trans, msat_ltl = \
                test_module.check_ltl(menv, enc)
            if hasattr(test_module, "diverging_symbs"):
                assert callable(test_module.diverging_symbs)
                div_symbs = test_module.diverging_symbs(menv)
                assert all(div_s in msat_symbs.keys() for div_s in div_symbs)
                for div_s in div_symbs:
                    msat_symbs, msat_init, msat_trans, msat_ltl = \
                        encode_diverging(menv, enc, div_s,
                                         msat_symbs, msat_init,
                                         msat_trans, msat_ltl)

            if spec_file is None:
                # tableau construction
                ts = enc.encode(msat_symbs, msat_ltl)
                init = mgr.And(convert(msat_init), convert(ts.init()))
                trans = mgr.And(convert(msat_trans), convert(ts.trans()))
                fairness = mgr.Not(convert(ts.prop()))
                assert all(symb_is_curr(s) for s in get_free_vars(init))
                assert all(symb_is_curr(s) for s in get_free_vars(fairness))
                symbols = frozenset(chain(get_free_vars(init),
                                          get_free_vars(fairness),
                                          (s if symb_is_curr(s)
                                           else symb2curr(env, s)
                                           for s in get_free_vars(trans))))
                fairness = to_c(env, fairness)
            else:
                init = convert(msat_init)
                trans = convert(msat_trans)
                symbols = frozenset(chain(get_free_vars(init),
                                          (convert(m_s) for m_s in msat_symbs),
                                          (s if symb_is_curr(s)
                                           else symb2curr(env, s)
                                           for s in get_free_vars(trans))))
                ltl = f"A ({transl_ltl(env, menv, enc, convert, msat_ltl)})"
                ultimate_ltl = transl_ultimate_ltl(env, menv, enc, convert,
                                                   msat_ltl)
    assert all(symb_is_curr(s) for s in symbols)
    init = to_c(env, init)
    trans = to_c(env, trans)
    serialize = env.serializer.serialize
    curr2next = {s: symb2next(env, s) for s in symbols}
    # contains_real = False
    decls = ""
    for s, x_s in curr2next.items():
        s_type = s.symbol_type()
        if s_type.is_int_type():
            type_str = "int"
        elif s_type.is_bool_type():
            type_str = "bool"
        else:
            assert s_type.is_real_type()
            # contains_real = True
            type_str = "float"
        decls += f"{type_str} {serialize(s)}, {serialize(x_s)};\n"

    curr_nondet = ""
    next_nondet = ""
    step_assign = ""
    serialize = env.serializer.serialize
    for s, x_s in curr2next.items():
        s_type = s.symbol_type()
        if s_type.is_int_type():
            fun = "__VERIFIER_nondet_int()"
        elif s_type.is_real_type():
            fun = "__VERIFIER_nondet_float()"
        else:
            assert s_type.is_bool_type()
            fun = "__VERIFIER_nondet_bool()"
        curr_nondet += f"  {serialize(s)} = {fun};\n"
        next_nondet += f"    {serialize(x_s)} = {fun};\n"
        step_assign += f"    {serialize(s)} = {serialize(x_s)};\n"

    assert isinstance(decls, str)
    assert isinstance(curr_nondet, str)
    assert isinstance(init, str)
    assert isinstance(trans, str)
    assert isinstance(next_nondet, str)
    assert isinstance(step_assign, str)
    if spec_file is not None:
        assert ltl is not None
        assert isinstance(ltl, str)
        assert ultimate_ltl is not None
        assert isinstance(ultimate_ltl, str)
        with open(spec_file, 'w') as out_f:
            out_f.write(ltl)
        with open(c_file, 'w') as out_f:
            out_f.write(c_ltl_template.format(decl_symbs=decls,
                                              curr_nondet=curr_nondet,
                                              init=init, next_nondet=next_nondet,
                                              trans=trans,
                                              step_assign=step_assign,
                                              ultimate_ltl=ultimate_ltl))
    else:
        with open(c_file, 'w') as out_f:
            out_f.write(c_template.format(decl_symbs=decls,
                                          curr_nondet=curr_nondet,
                                          init=init, next_nondet=next_nondet,
                                          trans=trans,
                                          step_assign=step_assign,
                                          fair=fairness))


def transl_ltl(env, menv, enc, convert, ltl):
    # arity = mathsat.msat_term_arity(ltl)
    # assert arity in {0, 1, 2}
    # if arity == 0:
    #     assert not enc.is_ltl(ltl)
    #     return to_c(convert(ltl))
    # args = [mathsat.msat_term_get_arg(ltl, i) for i in range(arity)]
    # args = [transl_ltl(menv, enc, convert, arg) for arg in args]
    if enc.is_X(ltl):
        assert mathsat.msat_term_arity(ltl) == 1
        arg = transl_ltl(env, menv, enc, convert,
                         mathsat.msat_term_get_arg(ltl, 0))
        return f"(X {arg})"
    if enc.is_U(ltl):
        assert mathsat.msat_term_arity(ltl) == 2
        arg0 = transl_ltl(env, menv, enc, convert,
                          mathsat.msat_term_get_arg(ltl, 0))
        arg1 = transl_ltl(env, menv, enc, convert,
                          mathsat.msat_term_get_arg(ltl, 1))
        return f"({arg0} U {arg1})"
    if enc.is_F(ltl):
        assert mathsat.msat_term_arity(ltl) == 1
        arg = transl_ltl(env, menv, enc, convert,
                         mathsat.msat_term_get_arg(ltl, 0))
        return f"(F {arg})"
    if enc.is_G(ltl):
        assert mathsat.msat_term_arity(ltl) == 1
        arg = transl_ltl(env, menv, enc, convert,
                         mathsat.msat_term_get_arg(ltl, 0))
        return f"(G {arg})"
    if mathsat.msat_term_is_and(menv, ltl):
        assert mathsat.msat_term_arity(ltl) == 2
        arg0 = transl_ltl(env, menv, enc, convert,
                          mathsat.msat_term_get_arg(ltl, 0))
        arg1 = transl_ltl(env, menv, enc, convert,
                          mathsat.msat_term_get_arg(ltl, 1))
        return f"( {arg0} && {arg1})"
    if mathsat.msat_term_is_or(menv, ltl):
        assert mathsat.msat_term_arity(ltl) == 2
        arg0 = transl_ltl(env, menv, enc, convert,
                          mathsat.msat_term_get_arg(ltl, 0))
        arg1 = transl_ltl(env, menv, enc, convert,
                          mathsat.msat_term_get_arg(ltl, 1))
        return f"( {arg0} || {arg1})"
    if mathsat.msat_term_is_iff(menv, ltl):
        assert mathsat.msat_term_arity(ltl) == 2
        arg0 = transl_ltl(env, menv, enc, convert,
                          mathsat.msat_term_get_arg(ltl, 0))
        arg1 = transl_ltl(env, menv, enc, convert,
                          mathsat.msat_term_get_arg(ltl, 1))
        return f"({arg0} <-> {arg1})"
    if mathsat.msat_term_is_not(menv, ltl):
        assert mathsat.msat_term_arity(ltl) == 1
        arg = transl_ltl(env, menv, enc, convert,
                         mathsat.msat_term_get_arg(ltl, 0))
        return f"(! {arg})"
    assert not enc.is_ltl(ltl)
    ltl = convert(ltl)
    return to_c(env, ltl)


def transl_ultimate_ltl(env, menv, enc, convert, ltl):
    if enc.is_X(ltl):
        assert mathsat.msat_term_arity(ltl) == 1
        arg = transl_ultimate_ltl(env, menv, enc, convert,
                                  mathsat.msat_term_get_arg(ltl, 0))
        return f"(X {arg})"
    if enc.is_U(ltl):
        assert mathsat.msat_term_arity(ltl) == 2
        arg0 = transl_ultimate_ltl(env, menv, enc, convert,
                                   mathsat.msat_term_get_arg(ltl, 0))
        arg1 = transl_ultimate_ltl(env, menv, enc, convert,
                                   mathsat.msat_term_get_arg(ltl, 1))
        return f"({arg0} U {arg1})"
    if enc.is_F(ltl):
        assert mathsat.msat_term_arity(ltl) == 1
        arg = transl_ultimate_ltl(env, menv, enc, convert,
                                  mathsat.msat_term_get_arg(ltl, 0))
        return f"(<> {arg})"
    if enc.is_G(ltl):
        assert mathsat.msat_term_arity(ltl) == 1
        arg = transl_ultimate_ltl(env, menv, enc, convert,
                                  mathsat.msat_term_get_arg(ltl, 0))
        return f"([] {arg})"
    if mathsat.msat_term_is_and(menv, ltl):
        assert mathsat.msat_term_arity(ltl) == 2
        arg0 = transl_ultimate_ltl(env, menv, enc, convert,
                          mathsat.msat_term_get_arg(ltl, 0))
        arg1 = transl_ultimate_ltl(env, menv, enc, convert,
                          mathsat.msat_term_get_arg(ltl, 1))
        return f"( {arg0} && {arg1})"
    if mathsat.msat_term_is_or(menv, ltl):
        assert mathsat.msat_term_arity(ltl) == 2
        arg0 = transl_ultimate_ltl(env, menv, enc, convert,
                                   mathsat.msat_term_get_arg(ltl, 0))
        arg1 = transl_ultimate_ltl(env, menv, enc, convert,
                                   mathsat.msat_term_get_arg(ltl, 1))
        return f"( {arg0} || {arg1})"
    if mathsat.msat_term_is_iff(menv, ltl):
        assert mathsat.msat_term_arity(ltl) == 2
        arg0 = transl_ultimate_ltl(env, menv, enc, convert,
                                   mathsat.msat_term_get_arg(ltl, 0))
        arg1 = transl_ultimate_ltl(env, menv, enc, convert,
                                   mathsat.msat_term_get_arg(ltl, 1))
        return f"({arg0} <==> {arg1})"
    if mathsat.msat_term_is_not(menv, ltl):
        assert mathsat.msat_term_arity(ltl) == 1
        arg = transl_ultimate_ltl(env, menv, enc, convert,
                                  mathsat.msat_term_get_arg(ltl, 0))
        return f"(! {arg})"
    if mathsat.msat_term_is_atom(menv, ltl):
        assert not enc.is_ltl(ltl)
        ltl = convert(ltl)
        return f"AP({to_c(env, ltl)})"
    assert False, str(ltl)


def main(out_dir: str, keep_ltl: bool, benchmarks):
    assert isinstance(benchmarks, (set, frozenset, list))
    assert os.path.isdir(out_dir)
    pop_env()  # do not use pysmt's environment stack.
    ext = ".py"
    bench_files = set()
    benchmarks = list(benchmarks)
    while benchmarks:
        _curr_path = benchmarks.pop()
        curr_path = os.path.abspath(_curr_path)
        if os.path.isfile(curr_path) and curr_path.endswith(ext):
            bench_files.add((os.path.basename(_curr_path)[:-len(ext)],
                             curr_path))
        elif os.path.isdir(curr_path):
            benchmarks.extend(os.path.join(curr_path, f_name)
                              for f_name in os.listdir(curr_path))

    for label, test_file in sorted(bench_files):
        assert os.path.isfile(test_file)
        # print("\n\nTranslating: `{}`".format(label))
        c_file = "{}.c".format(label)
        c_file = os.path.join(out_dir, c_file)
        spec_file = None
        if keep_ltl:
            spec_file = f"{label}.ctlstar"
            spec_file = os.path.join(out_dir, spec_file)
        translate(test_file, c_file, spec_file)


def getopts():
    p = argparse.ArgumentParser()
    p.add_argument("-o", "--output", type=str,
                   help="output directory")
    p.add_argument("-ltl", "--keep-ltl", default=False,
                   action="store_true",
                   help="Write LTL property in file")
    p.add_argument("benchmarks", nargs="+",
                   help="files or directories containing pyrank input files")

    return p.parse_args()


if __name__ == "__main__":
    opts = getopts()
    main(opts.output, opts.keep_ltl == 1, opts.benchmarks)
