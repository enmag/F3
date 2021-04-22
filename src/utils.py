from typing import Generator
import io
from collections.abc import Iterable

from pysmt.formula import FormulaManager
from pysmt.fnode import FNode
from pysmt.shortcuts import And
from pysmt.smtlib.script import smtlibscript_from_formula
from pysmt.logics import QF_NRA

from smv_prefixes import NEXT_MONITOR_PREFIX


VERBOSE = 0


def set_verbosity(val: int):
    global VERBOSE
    assert isinstance(val, int)
    VERBOSE = val


def get_verbosity() -> int:
    global VERBOSE
    return VERBOSE


def log(msg: str, lvl: int = 5) -> None:
    assert isinstance(msg, str)
    if get_verbosity() >= lvl:
        print(msg, flush=__debug__)


def pysmt_dump_whole_expr() -> None:
    # workaround to print whole expressions.
    FNode.__str__ = FNode.serialize


def to_smt2(*formulas, logic=QF_NRA):
    script = smtlibscript_from_formula(And(*formulas), logic=logic)
    buf = io.StringIO()
    script.serialize(buf)
    return buf.getvalue()


def name_next(symb: str) -> str:
    """return smv monitor symbol for next assignment of input symb"""
    assert isinstance(symb, str)
    return "{}{}".format(NEXT_MONITOR_PREFIX, symb)


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
    str_s = s.symbol_name()
    assert not name_is_next(str_s)
    return mgr.Symbol(name_next(str_s), s.symbol_type())


def to_next(mgr: FormulaManager, expr: FNode, symbols: Iterable) -> FNode:
    """Replace symbols with the corresponding monitor for next(symbol)"""
    assert isinstance(mgr, FormulaManager)
    assert isinstance(expr, FNode)
    assert isinstance(symbols, Iterable)
    env = mgr.env
    subs = {}
    for s in symbols:
        assert s.is_symbol(), "{}".format(s)
        subs[s] = mgr.Symbol(name_next(s.symbol_name()), s.symbol_type())
    return env.substituter.substitute(expr, subs)


def symb_to_curr(mgr: FormulaManager, n_s: FNode) -> FNode:
    """Get current assignment symbol"""
    str_n_s = n_s.symbol_name()
    assert name_is_next(str_n_s)
    return mgr.get_symbol(name_next_to_curr(str_n_s))


def to_curr(mgr: FormulaManager, expr: FNode, symbols: Iterable) -> FNode:
    """Replace next symbols with current symbols"""
    assert isinstance(mgr, FormulaManager)
    assert isinstance(expr, FNode)
    assert isinstance(symbols, Iterable)
    assert expr in mgr.formulae.values()
    assert all(e in mgr.formulae.values() for e in expr.get_atoms())

    env = mgr.env
    subs = {}
    for s in symbols:
        n_s = name_next(s.symbol_name())
        if n_s in mgr.symbols:
            n_s = mgr.get_symbol(n_s)
            subs[n_s] = s
    return env.substituter.substitute(expr, subs)


def default_key(x: FNode) -> tuple:
    assert isinstance(x, FNode)
    return (x.is_constant(), x.node_type(), x.node_id())


def assign_to_fnodes(mgr: FormulaManager, assign: dict) -> Generator[FNode,
                                                                     None,
                                                                     None]:
    assert isinstance(assign, dict)
    assert all(isinstance(k, FNode) for k in assign.keys())
    assert all(isinstance(v, FNode) for v in assign.values())
    assert all(k in mgr.formulae.values() for k in assign.keys())
    assert all(v in mgr.formulae.values() for v in assign.values())
    assert all(v.is_constant() for v in assign.values())
    yield from (k if v.is_true() else
                mgr.Not(k) if v.is_false() else
                mgr.Equals(k, v)
                for k, v in assign.items())
