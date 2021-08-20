from typing import Optional, Iterator, Iterable, FrozenSet, Tuple, List, Dict
import io
from math import ceil, log as mlog
from itertools import chain

from pysmt.environment import Environment as PysmtEnv
from pysmt.formula import FormulaManager
from pysmt.fnode import FNode
import pysmt.typing as types
from pysmt.shortcuts import And
from pysmt.smtlib.script import smtlibscript_from_formula
from pysmt.logics import QF_NRA

from smv_prefixes import NEXT_MONITOR_PREFIX
from rewritings import TimesDistributor


__VERBOSE = 0


def set_verbosity(val: int):
    global __VERBOSE
    assert isinstance(val, int)
    __VERBOSE = val


def get_verbosity() -> int:
    global __VERBOSE
    return __VERBOSE


def log(msg: str, lvl: int = 5) -> None:
    assert isinstance(msg, str)
    if get_verbosity() >= lvl:
        print(msg, flush=__debug__)


def pysmt_dump_whole_expr() -> None:
    # workaround to print whole expressions.
    FNode.__str__ = FNode.serialize


def to_smt2(env: PysmtEnv, *formulas, logic=QF_NRA) -> str:
    assert isinstance(env, PysmtEnv)
    script = smtlibscript_from_formula(env.formula_manager.And(*formulas),
                                       logic=logic, env=env)
    with io.StringIO() as buf:
        script.serialize(buf, env=env)
        return buf.getvalue()


def name_next(symb: str) -> str:
    """return smv monitor symbol for next assignment of input symb"""
    assert isinstance(symb, str)
    return f"{NEXT_MONITOR_PREFIX}{symb}"


def name_is_next(symb: str) -> bool:
    """True iff symb refers to next assignment"""
    assert isinstance(symb, str)
    return symb.startswith(NEXT_MONITOR_PREFIX)


def name_next_to_curr(symb: str) -> str:
    """return smv monitor symbol for current assignment of input symb"""
    assert name_is_next(symb)
    return symb[len(NEXT_MONITOR_PREFIX):]


def symb_is_next(symb: FNode) -> bool:
    """True iff symb refers to next assignment"""
    assert isinstance(symb, FNode)
    assert symb.is_symbol()
    return symb.symbol_name().startswith(NEXT_MONITOR_PREFIX)


def symb_is_curr(symb: FNode) -> bool:
    """True iff symb does not refer to next assignment"""
    return not symb_is_next(symb)


def symb_to_next(mgr: FormulaManager, s: FNode) -> FNode:
    """Get monitor for next(s)"""
    assert isinstance(mgr, FormulaManager)
    assert isinstance(s, FNode)
    assert s in mgr.get_all_symbols()
    assert not name_is_next(s.symbol_name())
    return mgr.Symbol(name_next(s.symbol_name()), s.symbol_type())


def to_next(mgr: FormulaManager, expr: FNode, symbols: Iterable) -> FNode:
    """Replace symbols with the corresponding monitor for next(symbol)"""
    assert isinstance(mgr, FormulaManager)
    assert isinstance(expr, FNode)
    assert isinstance(symbols, Iterable)
    assert all(s in mgr.get_all_symbols() for s in symbols)
    return mgr.env.substituter.substitute(expr,
                                          {s: symb_to_next(mgr, s)
                                           for s in symbols})


def symb_to_curr(mgr: FormulaManager, x_s: FNode) -> FNode:
    """Get current assignment symbol"""
    assert name_is_next(x_s.symbol_name())
    return mgr.Symbol(name_next_to_curr(x_s.symbol_name()), x_s.symbol_type())


def to_curr(mgr: FormulaManager, expr: FNode, symbols: Iterable) -> FNode:
    """Replace next symbols with current symbols"""
    assert isinstance(mgr, FormulaManager)
    assert isinstance(expr, FNode)
    assert isinstance(symbols, Iterable)
    assert expr in mgr.formulae.values()
    assert all(e in mgr.formulae.values() for e in mgr.env.ao.get_atoms(expr))
    return mgr.env.substituter.substitute(expr,
                                          {symb_to_next(mgr, s): s
                                           for s in symbols})


def default_key(x: FNode) -> tuple:
    assert isinstance(x, FNode)
    return (x.is_constant(), x.node_type(), x.node_id())


def is_atom(p: FNode) -> bool:
    """Test whether the formula is an atomic boolean predicate

        A literal is an atom, a theory relation is an atom.
        A non-boolean constant is not an atom.
        """
    assert isinstance(p, FNode)
    return p.is_literal() or p.is_theory_relation() or \
        p.is_bool_constant()


def is_not_true(p: FNode) -> bool:
    assert isinstance(p, FNode)
    return not p.is_true()


def assign2fnode(env: PysmtEnv, k: FNode, v: FNode) -> FNode:
    assert isinstance(env, PysmtEnv)
    assert isinstance(k, FNode)
    assert isinstance(v, FNode)
    assert k in env.formula_manager.formulae.values()
    assert v in env.formula_manager.formulae.values()
    assert env.stc.walk(k) == env.stc.walk(v)
    mgr = env.formula_manager
    tc = env.stc.walk
    if not is_atom(k) or not tc(k).is_bool_type():
        return mgr.Equals(k, v)
    if v.is_true():
        assert v is mgr.TRUE()
        return k
    if v.is_false():
        assert v is mgr.FALSE()
        return mgr.Not(k)
    assert tc(k).is_bool_type()
    assert tc(v).is_bool_type()
    return mgr.Iff(k, v)


def assign2fnodes(env: PysmtEnv,
                  *assigns: Dict[FNode, FNode]) -> Iterator[FNode]:
    assert isinstance(env, PysmtEnv)
    assert all(isinstance(assign, dict) for assign in assigns)
    assert all(isinstance(k, FNode) for assign in assigns for k in assign)
    assert all(k in env.formula_manager.formulae.values()
               for assign in assigns for k in assign)
    assert all(isinstance(v, FNode)
               for assign in assigns for v in assign.values())
    assert all(v in env.formula_manager.formulae.values()
               for assign in assigns for v in assign.values())
    assert all(not k.is_literal() or env.stc.get_type(k).is_bool_type()
               for assign in assigns for k in assign)

    yield from (assign2fnode(env, k, v)
                for k, v in chain.from_iterable(assign.items()
                                                for assign in assigns))


def new_symb(mgr: FormulaManager, base: str, s_type) -> FNode:
    """Return fresh symbol of the given type"""
    assert isinstance(mgr, FormulaManager)
    assert s_type in {types.BOOL, types.INT, types.REAL}
    assert isinstance(base, str)
    assert "%d" not in base
    return mgr.new_fresh_symbol(s_type, f"{base}%d")


def linear_comb(env: PysmtEnv, symbs: FrozenSet[FNode],
                prefix: str,
                idx: Optional[int] = None,
                totime=None) -> Tuple[FNode, List[FNode]]:
    """Return FNode expr representing linear combination of symbs and
    list of parameters"""
    assert isinstance(symbs, frozenset)
    assert all(isinstance(s, FNode) for s in symbs)
    assert all(s in env.formula_manager.formulae.values() for s in symbs)
    assert isinstance(prefix, str)
    assert idx is None or totime is not None
    assert idx is None or isinstance(idx, int), idx
    assert all(env.stc.get_type(s).is_int_type() for s in symbs) or \
        all(env.stc.get_type(s).is_real_type() for s in symbs)

    m_type = types.REAL
    if symbs and env.stc.get_type(next(iter(symbs))).is_int_type():
        m_type = types.INT

    mgr = env.formula_manager
    k = new_symb(mgr, f"{prefix}_k", m_type)
    res = [k]
    params = [k]
    for s in symbs:
        if idx is not None:
            assert totime is not None
            s = totime(s, idx)
        coeff = new_symb(mgr, f"{prefix}_c", m_type)
        params.append(coeff)
        res.append(mgr.Times(coeff, s))
    res = mgr.Plus(res)
    assert all(p in mgr.get_all_symbols() for p in params)
    return res, params


def new_enum(env: PysmtEnv, v_name: str, enum_size: int) -> \
        Tuple[List[FNode], List[FNode]]:
    """Create boolean symbols to encode `enum_size` different values"""
    assert isinstance(env, PysmtEnv)
    assert isinstance(v_name, str)
    assert isinstance(enum_size, int)
    assert enum_size > 1

    mgr = env.formula_manager
    num_bits = ceil(mlog(enum_size, 2))
    b_vars = [new_symb(mgr, f"{v_name}{idx}", types.BOOL)
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
