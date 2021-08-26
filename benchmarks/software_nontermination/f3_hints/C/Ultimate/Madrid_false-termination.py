from typing import FrozenSet, Tuple

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
    x = mgr.Symbol("x", types.INT)
    x_pc = symb_to_next(mgr, pc)
    x_x = symb_to_next(mgr, x)

    m_1 = mgr.Int(-1)
    i_0 = mgr.Int(0)
    i_1 = mgr.Int(1)
    i_2 = mgr.Int(2)
    i_7 = mgr.Int(7)

    pc0 = mgr.Equals(pc, i_0)
    pc1 = mgr.Equals(pc, i_1)
    x_pc1 = mgr.Equals(x_pc, i_1)
    pc2 = mgr.Equals(pc, i_2)
    x_pc2 = mgr.Equals(x_pc, i_2)
    pcend = mgr.Equals(pc, m_1)
    x_pcend = mgr.Equals(x_pc, m_1)

    init = mgr.And(pc0, mgr.Equals(x, i_7))
    cfg = []
    # pc = 0 -> pc = 1
    cfg.append(mgr.Implies(pc0, x_pc1))
    # pc = 1 & TRUE -> pc' = 2
    cfg.append(mgr.Implies(mgr.And(pc1, mgr.TRUE()), x_pc2))
    # pc = 1 & !TRUE -> pc' = 2
    cfg.append(mgr.Implies(mgr.And(pc1, mgr.Not(mgr.TRUE())), x_pcend))
    # pc = 2 -> pc' = 1
    cfg.append(mgr.Implies(pc2, x_pc1))
    # pc = -1 -> pc' = -1
    cfg.append(mgr.Implies(pcend, x_pcend))

    trans = []
    # pc = 0 -> x' = x
    trans.append(mgr.Implies(pc0, mgr.Equals(x_x, x)))
    # pc = 1 -> x' = x
    trans.append(mgr.Implies(pc1, mgr.Equals(x_x, x)))
    # pc = 2 -> x' = 2
    trans.append(mgr.Implies(pc2, mgr.Equals(x_x, i_2)))
    # pc = end -> x' = x
    trans.append(mgr.Implies(pcend, mgr.Equals(x_x, x)))

    trans = mgr.And(*cfg, *trans)

    fairness = mgr.Not(mgr.Equals(pc, m_1))
    symbols = frozenset([pc, x])
    return symbols, init, trans, fairness


def hints(env: PysmtEnv) -> FrozenSet[Hint]:
    assert isinstance(env, PysmtEnv)

    mgr = env.formula_manager
    pc = mgr.Symbol("pc", types.INT)
    x = mgr.Symbol("x", types.INT)
    symbs = frozenset([pc, x])

    x_x = symb_to_next(mgr, x)

    i_2 = mgr.Int(2)
    stutter = mgr.Equals(x_x, x)
    l0 = Location(env, mgr.Equals(x, i_2), mgr.TRUE(), stutterT=stutter)

    l0.set_progress(0, mgr.Equals(x_x, i_2))

    h_x = Hint("h_x", env, frozenset([x]), symbs)
    h_x.set_locs([l0])

    return frozenset([h_x])
