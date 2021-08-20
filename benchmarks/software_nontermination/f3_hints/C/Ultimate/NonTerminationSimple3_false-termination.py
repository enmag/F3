from typing import Tuple, FrozenSet

from pysmt.environment import Environment as PysmtEnv
from pysmt.fnode import FNode
import pysmt.typing as types

from utils import symb_to_next
from hint import Hint, Location


def transition_system(env: PysmtEnv) -> Tuple[FrozenSet[FNode], FNode, FNode,
                                              FNode]:
    assert isinstance(env, PysmtEnv)
    mgr = env.formula_manager
    pc = mgr.Symbol("pc", types.INT)
    x_pc = symb_to_next(mgr, pc)
    x = mgr.Symbol("x", types.INT)
    x_x = symb_to_next(mgr, x)
    c = mgr.Symbol("c", types.INT)
    x_c = symb_to_next(mgr, c)

    symbols = frozenset([pc, x, c])

    m_1 = mgr.Int(-1)

    ints = [mgr.Int(idx) for idx in range(2)]
    pcs = []
    x_pcs = []
    n_locs = 2
    for idx in range(n_locs):
        num = ints[idx]
        pcs.append(mgr.Equals(pc, num))
        x_pcs.append(mgr.Equals(x_pc, num))
    pcend = mgr.Equals(pc, m_1)
    x_pcend = mgr.Equals(x_pc, m_1)

    init = pcs[0]
    cfg = []
    # pc = 0 & x >= 0 -> pc' = 1
    cfg.append(mgr.Implies(mgr.And(pcs[0], mgr.GE(x, ints[0])), x_pcs[1]))
    # pc = 0 & !(x >= 0) -> pc' = -1
    cfg.append(mgr.Implies(mgr.And(pcs[0], mgr.Not(mgr.GE(x, ints[0]))),
                           x_pcend))
    # pc = 1 -> pc' = 0
    cfg.append(mgr.Implies(pcs[1], x_pcs[0]))
    # pc = -1 -> pc' = -1
    cfg.append(mgr.Implies(pcend, x_pcend))

    trans = []
    same = mgr.And(mgr.Equals(x_x, x), mgr.Equals(x_c, c))
    # pc = 0 -> x' = x & c' = c
    trans.append(mgr.Implies(pcs[0], same))
    # pc = 1 -> x' = x + c & c' = c
    trans.append(mgr.Implies(pcs[1], mgr.And(mgr.Equals(x_x, mgr.Plus(x, c)),
                                             mgr.Equals(x_c, c))))
    # pc = end -> x' = x & c' = c
    trans.append(mgr.Implies(pcend, same))

    trans = mgr.And(*cfg, *trans)

    fairness = mgr.Not(mgr.Equals(pc, m_1))
    return symbols, init, trans, fairness


def hints(env: PysmtEnv) -> FrozenSet[Hint]:
    assert isinstance(env, PysmtEnv)

    mgr = env.formula_manager
    pc = mgr.Symbol("pc", types.INT)
    x = mgr.Symbol("x", types.INT)
    c = mgr.Symbol("c", types.INT)
    symbs = frozenset([pc, x, c])

    x_c = symb_to_next(mgr, c)
    i_0 = mgr.Int(0)
    l0 = Location(env, mgr.Equals(c, i_0), mgr.TRUE())
    l0.set_progress(0, eq_0=mgr.Equals(x_c, c))
    h_c = Hint("h_c", env, frozenset([c]), symbs)
    h_c.set_locs([l0])

    x_x = symb_to_next(mgr, x)
    i_1 = mgr.Int(1)
    stutter = mgr.Equals(x_x, x)
    l0 = Location(env, mgr.GE(x, i_1), mgr.TRUE(), stutterT=stutter)
    l0.set_progress(0, eq_0=mgr.Equals(x_x, mgr.Plus(x, c)))
    h_x = Hint("h_x", env, frozenset([x]), symbs)
    h_x.set_locs([l0])

    return frozenset([h_c, h_x])
