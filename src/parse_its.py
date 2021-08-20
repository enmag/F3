from typing import Tuple, FrozenSet, Dict, Set, List, Optional
from collections import defaultdict
import re

from pysmt.environment import Environment as PysmtEnv
from pysmt.fnode import FNode
from pysmt.smtlib.parser import SmtLibParser

from utils import new_enum, symb_to_next, to_next


def parse_its(env: PysmtEnv, in_file: str) -> Tuple[FrozenSet[FNode],
                                                    FNode, FNode, FNode]:
    """Parse integer transition system from in_file.
    Return set of symbols, initial constraints, transition relation and
    fairness condition.
    Input syntax described in:
    https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/SMTPushdownPrograms.pdf"""
    assert isinstance(env, PysmtEnv)
    assert False, "Not supported"
    # TODO: map Loc to int
    # TODO: build FNode representing init and trans.
    o_norm = env.formula_manager.normalize
    i_env = PysmtEnv()
    i_mgr = i_env.formula_manager
    get_free_vars = i_env.fvo.get_free_variables
    substitute = i_env.substituter.substitute
    parser = SmtLibParser(env=i_env)
    with open(in_file, 'r') as in_f:
        script = parser.get_script(in_f)
    assert len(i_env.type_manager._custom_types) == 1
    assert list(i_env.type_manager._custom_types_decl.keys())[0] == "Loc"

    loc_type = i_env.type_manager.Type("Loc")
    assert len(i_env.type_manager._custom_types) == 1
    locconst2val = {}
    val = 0
    for cmd in script.filter_by_command_name("declare-const"):
        assert len(cmd.args) == 2
        c_name, c_type = cmd.args
        assert isinstance(c_name, FNode)
        if c_type == loc_type:
            locconst2val[c_name] = i_mgr.Int(val)
            val += 1

    # fun name to (parameters, definition)
    funcs = {cmd.args[0]: (cmd.args[1], cmd.args[3])
             for cmd in script.filter_by_command_name("define-fun")}
    assert "init_main" in funcs
    assert "next_main" in funcs

    fun2symbs: Dict[str, List[FNode]] = {}
    fun2init = {}
    fun2next = {}
    fun2calls = defaultdict(list)
    fun2returns = defaultdict(list)
    dependencies = defaultdict(set)
    re_init = re.compile(r"init_(?P<name>\S+)")
    re_next = re.compile(r"next_(?P<name>\S+)")
    re_fun_call = re.compile(r"(?P<caller>\S+)_call_(?P<callee>\S+)")
    re_fun_return = re.compile(r"(?P<callee>\S+)_return_(?P<caller>\S+)")
    other_cmds = []
    # handle init and next.
    for cmd in script.filter_by_command_name("define-fun"):
        assert len(cmd.args) == 4
        full_name, params, ret_type, definition = cmd.args
        match = re_init.fullmatch(full_name)
        if match:
            assert ret_type.is_bool_type()
            name = match.group("name")
            assert name not in fun2init
            symbs = fun2symbs.get(name)
            if symbs is None:
                symbs = params2symbs(i_env, params)
                fun2symbs[name] = symbs
            assert len(symbs) == len(params)
            subs = {**locconst2val,
                    **{p: s for p, s in zip(params, symbs)}}
            definition = substitute(definition, subs)
            fun2init[name] = definition
            continue
        match = re_next.fullmatch(full_name)
        if match:
            assert ret_type.is_bool_type()
            name = match.group("name")
            assert name not in fun2next
            symbs = fun2symbs.get(name)
            if symbs is None:
                assert len(params) % 2 == 0
                assert all(s.symbol_type() == x_s.symbol_type()
                           for s, x_s in zip(params, params[len(params)//2:]))
                symbs = params2symbs(i_env, params[:len(params)//2])
                fun2symbs[name] = symbs
            assert 2 * len(symbs) == len(params)
            all_symbs = symbs + [symb_to_next(i_mgr, s) for s in symbs]
            definition = substitute(definition, {p: s for p, s in zip(params, all_symbs)})
            fun2next[name] = definition
            continue
        if full_name not in {"cfg_init", "cfg_trans2", "cfg_trans3"}:
            other_cmds.append(cmd)

    # handle function calls and returns.
    for cmd in other_cmds:
        full_name, params, ret_type, definition = cmd.args

        match = re_fun_call.fullmatch(full_name)
        if match:
            assert ret_type.is_bool_type()
            caller = match.group("caller")
            assert caller in fun2symbs
            caller_symbs = fun2symbs[caller]
            callee = match.group("callee")
            assert callee in fun2symbs
            callee_x_symbs = [symb_to_next(i_mgr, s) for s in fun2symbs[callee]]
            assert len(params) == len(caller_symbs) + len(callee_x_symbs)
            dependencies[caller].add(callee)
            definition = substitute(definition,
                                    {p: s for p, s in zip(params, caller_symbs + callee_x_symbs)})
            fun2calls[caller].append((callee, definition))
            continue
        match = re_fun_return.fullmatch(full_name)
        if match:
            assert ret_type.is_bool_type()
            caller = match.group("caller")
            assert caller in fun2symbs
            caller_symbs = fun2symbs[caller]
            x_caller_symbs = [symb_to_next(i_mgr, s) for s in caller_symbs]
            callee = match.group("callee")
            assert callee in fun2symbs
            callee_symbs = fun2symbs[callee]
            caller_x_symbs = [symb_to_next(i_mgr, s) for s in fun2symbs[caller]]
            assert len(params) == len(callee_symbs) + len(caller_symbs) + len(caller_x_symbs)
            definition = substitute(definition,
                                    {p: s for p, s in zip(params, callee_symbs + caller_symbs + x_caller_symbs)})
            fun2returns[callee].append((caller, definition))
            continue
        print(f"Unknown `define-fun`: {cmd}")

    fun_names = frozenset(fun_names)
    rec = is_recursive("main", dependencies)
    if rec:
        raise Exception(f"recursive functions are not implemented: {rec}")
    if "main" not in fun_names:
        raise Exception("could not find `main` function")
    if len(fun2init) != 1:
        raise Exception("found multiple inits")
    if "main" not in fun2init:
        raise Exception("could not find init_main")
    if "main" not in fun2next:
        raise Exception("could not find next_main")
    init = fun2init["main"][2]


def params2symbs(i_env: PysmtEnv, params: List[FNode]) -> List[FNode]:
    i_mgr = i_env.formula_manager
    res = []
    for p in params:
        name = p.symbol_name()
        if name.startswith("__"):
            name = name[2:]
        res.append(i_mgr.Symbol(name, p.symbol_type()))
    return res


def is_recursive(root: str, deps: Dict[str, Set[str]]) -> Optional[List[str]]:
    stack = [root]
    context = set(stack)
    visited = set()
    while stack:
        curr = stack[-1]
        if curr in visited:
            stack.pop()
            context.remove(curr)
        else:
            if len(context & deps[curr]) > 0:
                stack.append(list(context & deps[curr])[0])
                return stack
            stack.extend(deps)
            context.update(deps)
            visited.add(curr)
    return None


def main(argv):
    import os
    assert os.path.isfile(argv[1])
    parse_its(PysmtEnv(), argv[1])


if __name__ == "__main__":
    import sys
    main(sys.argv)
