from typing import (Tuple, List, FrozenSet, Set, Dict, Iterator, Optional,
                    Union, Iterable)
from math import ceil, log
from re import compile as re_compile

from pysmt.environment import Environment as PysmtEnv
from pysmt.fnode import FNode
import pysmt.typing as types


_NEXT_SYMB_PREF = "_x"
_FROZEN_SYMB_PREF = "_f"
_PARAM_SYMB_PREF = "_p"
_TIME_RE = re_compile(r"@(\d+)$")


def fnode_key(x: FNode) -> tuple:
    assert isinstance(x, FNode)
    return (x.is_constant(), x.node_type(), x.node_id())


def new_symb(env: PysmtEnv, base: str, s_type=types.BOOL) -> FNode:
    """Return fresh symbol of the given type"""
    assert isinstance(env, PysmtEnv)
    assert s_type in {types.BOOL, types.INT, types.REAL}
    assert isinstance(base, str)
    assert "%d" not in base
    assert not base.startswith(_NEXT_SYMB_PREF)
    assert not base.startswith(_FROZEN_SYMB_PREF)
    assert not base.startswith(_PARAM_SYMB_PREF)
    assert "@" not in base
    return env.formula_manager.new_fresh_symbol(s_type, f"{base}%d")


def new_enum(env: PysmtEnv, name: str, enum_size: int) -> Tuple[List[FNode],
                                                                List[FNode]]:
    """Create boolean symbols to encode `enum_size` different values"""
    assert isinstance(env, PysmtEnv)
    assert isinstance(name, str)
    assert isinstance(enum_size, int)
    assert enum_size > 1

    mgr = env.formula_manager
    num_bits = ceil(log(enum_size, 2))
    b_vars = [new_symb(env, f"{name}{idx}", types.BOOL)
              for idx in range(num_bits)]
    vals = []
    for enum_val in range(enum_size):
        bit_val = format(enum_val, '0{}b'.format(num_bits))
        assert len(bit_val) == num_bits
        assert all(c in {'0', '1'} for c in bit_val)
        vals.append(mgr.And(b_vars[idx] if c == '1' else
                            mgr.Not(b_vars[idx])
                            for idx, c in enumerate(reversed(bit_val))))
    assert len(vals) == enum_size
    return b_vars, vals


def new_param(env: PysmtEnv, base: str, s_type=types.BOOL) -> FNode:
    """Return fresh parameter of the given type"""
    assert isinstance(env, PysmtEnv)
    assert s_type in {types.BOOL, types.INT, types.REAL}
    assert isinstance(base, str)
    assert "%d" not in base
    return env.formula_manager.new_fresh_symbol(s_type,
                                                f"{_PARAM_SYMB_PREF}{base}%d")


def new_frozen(env: PysmtEnv, base: str, s_type=types.BOOL) -> FNode:
    """Return fresh parameter of the given type"""
    assert isinstance(env, PysmtEnv)
    assert s_type in {types.BOOL, types.INT, types.REAL}
    assert isinstance(base, str)
    assert "%d" not in base
    return env.formula_manager.new_fresh_symbol(s_type,
                                                f"{_FROZEN_SYMB_PREF}{base}%d")


def name_is_next(name: str) -> bool:
    """True iff name refers to next assignment"""
    assert isinstance(name, str)
    return name.startswith(_NEXT_SYMB_PREF)


def name_is_frozen(name: str) -> bool:
    """True iff name refers to frozen symbol"""
    assert isinstance(name, str)
    return name.startswith(_FROZEN_SYMB_PREF)


def name_is_param(name: str) -> bool:
    """True iff name refers to parameter symbol"""
    assert isinstance(name, str)
    return name.startswith(_PARAM_SYMB_PREF)


def get_name_time(name: str) -> Tuple[str, Optional[int]]:
    """Return untimed name and time"""
    assert isinstance(name, str)
    # if name_is_frozen(name) or name_is_param(name):
    #     return None
    idx = name.rfind("@", 1, -1)
    return (name[:idx], int(name[idx+1:])) if idx != -1 else (name, None)


def get_time(name: str) -> Optional[int]:
    """Extract time of given name, None if not timed"""
    assert isinstance(name, str)
    # if name_is_frozen(name) or name_is_param(name):
    #     return None
    idx = name.rfind("@", 1, -1)
    return int(name[idx+1:]) if idx != -1 else None


def name_is_timed(name: str) -> bool:
    """True iff name is timed"""
    assert isinstance(name, str)
    return get_time(name) is not None


def name2next(name: str) -> str:
    """return name for next(name)"""
    assert isinstance(name, str)
    assert not name_is_timed(name)
    return f"{_NEXT_SYMB_PREF}{name}"


def name2curr(name: str) -> str:
    """return name for current assignment of input name"""
    assert name_is_next(name)
    assert not name_is_timed(name)
    return name[len(_NEXT_SYMB_PREF):]


def name2frozen(name: str) -> str:
    """return symbol name for frozen symbol"""
    assert isinstance(name, str)
    assert not name_is_timed(name)
    return f"{_FROZEN_SYMB_PREF}{name}"


def name2thawed(name: str) -> str:
    """return symbol name for thawed symbol"""
    assert isinstance(name, str)
    assert name_is_frozen(name)
    assert not name_is_timed(name)
    return name[len(_FROZEN_SYMB_PREF):]


def name2timed(name: str, time: int) -> str:
    """Return name representing the counterpart at the given time"""
    assert isinstance(name, str)
    assert isinstance(time, int)
    assert time >= 0
    assert not name_is_next(name)
    if name_is_frozen(name) or name_is_param(name):
        return name
    assert len(name) > 0
    assert len(str(time)) > 0
    return f"{name}@{time}"


def name2untimed(name: str) -> str:
    """Return name representing the untimed counterpart"""
    assert isinstance(name, str)
    idx = name.rfind("@", 1, -1)
    return name[:idx] if idx != -1 else name


def symb_is_next(symb: FNode) -> bool:
    """True iff symb refers to next assignment"""
    assert isinstance(symb, FNode)
    assert symb.is_symbol()
    return name_is_next(symb.symbol_name())


def symb_is_curr(symb: FNode) -> bool:
    """True iff symb does not refer to next assignment"""
    return not symb_is_next(symb)


def symb_is_frozen(symb: FNode) -> bool:
    """True iff symb is frozen symbol"""
    assert isinstance(symb, FNode)
    assert symb.is_symbol()
    return name_is_frozen(symb.symbol_name())


def symb_is_thawed(symb: FNode) -> bool:
    """True iff symb is not frozen symbol"""
    return not symb_is_frozen(symb)


def symb_is_param(symb: FNode) -> bool:
    """True iff symb is a parameter symbol"""
    assert isinstance(symb, FNode)
    assert symb.is_symbol()
    return name_is_param(symb.symbol_name())


def get_symb_time(symb: FNode) -> Optional[int]:
    """Extract time of given symb, None if not timed"""
    assert isinstance(symb, FNode)
    assert symb.is_symbol()
    return get_time(symb.symbol_name())


def symb_is_timed(symb: FNode) -> bool:
    """True iff given symb is timed"""
    return get_symb_time(symb) is not None


def symb2next(env: PysmtEnv, s: FNode) -> FNode:
    """Get symbol representing for next(s)"""
    assert isinstance(env, PysmtEnv)
    assert isinstance(s, FNode)
    assert s.is_symbol()
    assert s in env.formula_manager.get_all_symbols()
    assert not name_is_next(s.symbol_name())
    return env.formula_manager.Symbol(name2next(s.symbol_name()),
                                      s.symbol_type())


def symb2curr(env: PysmtEnv, x_s: FNode) -> FNode:
    """Get current assignment symbol"""
    assert isinstance(env, PysmtEnv)
    assert isinstance(x_s, FNode)
    assert x_s.is_symbol()
    assert x_s in env.formula_manager.get_all_symbols()
    assert name_is_next(x_s.symbol_name())
    return env.formula_manager.Symbol(name2curr(x_s.symbol_name()),
                                      x_s.symbol_type())


def symb2frozen(env: PysmtEnv, s: FNode) -> FNode:
    """Get symbol representing frozen counterpart"""
    assert isinstance(env, PysmtEnv)
    assert isinstance(s, FNode)
    assert s.is_symbol()
    assert s in env.formula_manager.get_all_symbols()
    assert not symb_is_frozen(s)
    return env.formula_manager.Symbol(name2frozen(s.symbol_name()),
                                      s.symbol_type())


def symb2thawed(env: PysmtEnv, s: FNode) -> FNode:
    """Get symbol representing thawed counterpart"""
    assert isinstance(env, PysmtEnv)
    assert isinstance(s, FNode)
    assert s.is_symbol()
    assert s in env.formula_manager.get_all_symbols()
    assert symb_is_frozen(s)
    return env.formula_manager.Symbol(name2thawed(s.symbol_name()),
                                      s.symbol_type())


def symb2timed(env: PysmtEnv, s: FNode, time: int) -> FNode:
    assert isinstance(env, PysmtEnv)
    assert isinstance(s, FNode)
    assert s.is_symbol()
    assert s in env.formula_manager.get_all_symbols()
    assert not symb_is_timed(s)
    assert isinstance(time, int)
    assert time >= 0
    if symb_is_frozen(s) or symb_is_param(s):
        return s
    return env.formula_manager.Symbol(name2timed(s.symbol_name(), time),
                                      s.symbol_type())


def symb2untimed(env: PysmtEnv, s: FNode) -> FNode:
    assert isinstance(env, PysmtEnv)
    assert isinstance(s, FNode)
    assert s.is_symbol()
    assert s in env.formula_manager.get_all_symbols()
    assert symb_is_timed(s)
    if symb_is_frozen(s) or symb_is_param(s):
        return s
    return env.formula_manager.Symbol(name2untimed(s.symbol_name()),
                                      s.symbol_type())


def get_times(env: PysmtEnv, fm: FNode) -> FrozenSet[int]:
    assert isinstance(env, PysmtEnv)
    assert isinstance(fm, FNode)
    assert fm in env.formula_manager.formulae.values()
    res = set(get_symb_time(s) for s in env.fvo.get_free_variables(fm)
              if not symb_is_frozen(s) and not symb_is_param(s))
    res.discard(None)
    return frozenset(res)


def to_next(env: PysmtEnv, expr: FNode, symbs: Union[FrozenSet[FNode],
                                                     Set[FNode]]) -> FNode:
    """Replace each s in symbs with the corresponding next(s)"""
    assert isinstance(env, PysmtEnv)
    assert isinstance(expr, FNode)
    assert isinstance(symbs, (frozenset, set))
    assert all(isinstance(s, FNode) for s in symbs)
    assert all(s in env.formula_manager.get_all_symbols() for s in symbs)
    assert all(symb_is_curr(s) for s in symbs)
    return env.substituter.substitute(expr, {s: symb2next(env, s)
                                             for s in symbs})


def to_curr(env: PysmtEnv, expr: FNode, symbs: Union[FrozenSet[FNode],
                                                     Set[FNode]]) -> FNode:
    """Replace next symbols with current symbols"""
    assert isinstance(env, PysmtEnv)
    assert isinstance(expr, FNode)
    assert isinstance(symbs, (frozenset, set))
    assert all(isinstance(s, FNode) for s in symbs)
    assert all(s in env.formula_manager.get_all_symbols() for s in symbs)
    assert all(symb_is_curr(s) for s in symbs)
    return env.substituter.substitute(expr, {symb2next(env, s): s
                                             for s in symbs})


def is_atom(p: FNode) -> bool:
    """Test whether the formula is an atomic boolean predicate

        A literal is an atom, a theory relation is an atom.
        A non-boolean constant is not an atom.
        """
    assert isinstance(p, FNode)
    return p.is_literal() or p.is_theory_relation() or \
        p.is_bool_constant()


def not_rel(env: PysmtEnv, rel: FNode) -> FNode:
    assert isinstance(env, PysmtEnv)
    assert isinstance(rel, FNode)
    assert rel in env.formula_manager.formulae.values()
    mgr = env.formula_manager
    if rel.is_true():
        return mgr.FALSE()
    if rel.is_false():
        return mgr.TRUE()

    assert rel.is_le() or rel.is_lt()
    return mgr.LT(rel.arg(1), rel.arg(0)) if rel.is_le() else \
        mgr.LE(rel.arg(1), rel.arg(0))


def not_rels(env: PysmtEnv, rel: FNode) -> List[FNode]:
    """Return list of disjunctive predicates equivalent
    to negation of rel"""
    assert isinstance(env, PysmtEnv)
    assert isinstance(rel, FNode)
    assert rel in env.formula_manager.formulae.values()
    mgr = env.formula_manager
    if rel.is_true():
        return [mgr.FALSE()]
    if rel.is_false():
        return [mgr.TRUE()]

    arg0 = rel.arg(0)
    arg1 = rel.arg(1)
    if rel.is_equals():
        return [mgr.LT(arg1, arg0), mgr.LT(arg0, arg1)]

    assert rel.is_le() or rel.is_lt()
    return [mgr.LT(arg1, arg0) if rel.is_le() else mgr.LE(arg1, arg0)]


def assign2fnode(env: PysmtEnv, k: FNode, v: FNode) -> FNode:
    assert isinstance(env, PysmtEnv)
    assert isinstance(k, FNode)
    assert isinstance(v, FNode)
    assert k in env.formula_manager.formulae.values()
    assert v in env.formula_manager.formulae.values()
    assert env.stc.get_type(k) == env.stc.get_type(v)
    if v.is_true():
        return k
    if v.is_false():
        return env.formula_manager.Not(k)
    if env.stc.get_type(k).is_bool_type():
        return env.formula_manager.Iff(k, v)
    return env.formula_manager.Equals(k, v)


def assigns2fnodes(env: PysmtEnv,
                   assign: Dict[FNode, FNode]) -> Iterator[FNode]:
    assert isinstance(env, PysmtEnv)
    assert isinstance(assign, dict)
    assert all(isinstance(k, FNode) for k in assign)
    assert all(k in env.formula_manager.formulae.values()
               for k in assign)
    assert all(isinstance(v, FNode) for v in assign.values())
    assert all(v in env.formula_manager.formulae.values()
               for v in assign.values())
    assert all(not k.is_literal() or env.stc.get_type(k).is_bool_type()
               for k in assign)

    yield from (assign2fnode(env, k, v) for k, v in assign.items())


def linear_comb(env: PysmtEnv, symbs: Union[FrozenSet[FNode],
                                            Set[FNode]]) -> Tuple[FNode,
                                                                  Set[FNode]]:
    """Return FNode expr representing linear combination of symbs and
    list of parameters"""
    assert isinstance(env, PysmtEnv)
    assert isinstance(symbs, (frozenset, set))
    assert all(isinstance(s, FNode) for s in symbs)
    assert all(s in env.formula_manager.formulae.values() for s in symbs)
    assert all(env.stc.get_type(s).is_int_type() for s in symbs) or \
        all(env.stc.get_type(s).is_real_type() for s in symbs)

    m_type = types.REAL
    if symbs and env.stc.get_type(next(iter(symbs))).is_int_type():
        m_type = types.INT

    mgr = env.formula_manager
    k = new_param(env, "k", m_type)
    res = [k]
    params = set([k])
    for s in symbs:
        coeff = new_param(env, "c", m_type)
        params.add(coeff)
        res.append(mgr.Times(coeff, s))
    res = mgr.Plus(res)
    assert all(p in mgr.get_all_symbols() for p in params)
    return res, params


def flatten(fms: Union[FNode, Iterable[FNode], Iterator[FNode]],
            to_expand) -> Iterator[FNode]:
    fms = [fms] if isinstance(fms, FNode) else list(fms)
    assert all(isinstance(p, FNode) for p in fms)
    while fms:
        curr = fms.pop()
        if to_expand(curr):
            fms.extend(curr.args())
        else:
            assert isinstance(curr, FNode)
            yield curr
