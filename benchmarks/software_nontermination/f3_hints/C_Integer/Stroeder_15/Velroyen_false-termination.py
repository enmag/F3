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
    x = mgr.Symbol("x", types.INT)
    x_pc = symb_to_next(mgr, pc)
    x_x = symb_to_next(mgr, x)

    symbols = frozenset([pc, x])

    m_5 = mgr.Int(-5)
    m_1 = mgr.Int(-1)

    n_locs = 8
    max_int = 36
    ints = []
    pcs = []
    x_pcs = []
    for idx in range(n_locs):
        num = mgr.Int(idx)
        ints.append(num)
        pcs.append(mgr.Equals(pc, num))
        x_pcs.append(mgr.Equals(x_pc, num))

    for idx in range(n_locs, max_int):
        num = mgr.Int(idx)
        ints.append(num)

    pcend = mgr.Equals(pc, m_1)
    x_pcend = mgr.Equals(x_pc, m_1)

    init = pcs[0]

    cfg = []
    # pc = 0 & (x != 0) -> pc' = 1
    cond = mgr.Not(mgr.Equals(x, ints[0]))
    cfg.append(mgr.Implies(mgr.And(pcs[0], cond), x_pcs[1]))
    # pc = 0 & !(x != 0) -> pc' = -1
    cfg.append(mgr.Implies(mgr.And(pcs[0], mgr.Not(cond)), x_pcend))
    # pc = 1 & (-5 <= x <= 35) -> pc' = 2
    cond = mgr.And(mgr.LE(m_5, x), mgr.LE(x, ints[35]))
    cfg.append(mgr.Implies(mgr.And(pcs[1], cond), x_pcs[2]))
    # pc = 1 & !(-5 <= x <= 35) -> pc' = 7
    cfg.append(mgr.Implies(mgr.And(pcs[1], mgr.Not(cond)), x_pcs[7]))
    # pc = 2 & (x < 0) -> pc' = 3
    cond = mgr.LT(x, ints[0])
    cfg.append(mgr.Implies(mgr.And(pcs[2], cond), x_pcs[3]))
    # pc = 2 & !(x < 0) -> pc' = 4
    cond = mgr.LT(x, ints[0])
    cfg.append(mgr.Implies(mgr.And(pcs[2], cond), x_pcs[4]))
    # pc = 3 -> pc' = 0
    cfg.append(mgr.Implies(pcs[3], x_pcs[0]))
    # pc = 4 & (x > 30) -> pc' = l5
    cond = mgr.GT(x, ints[30])
    cfg.append(mgr.Implies(mgr.And(pcs[4], cond), x_pcs[5]))
    # pc = 4 & !(x > 30) -> pc' = l6
    cfg.append(mgr.Implies(mgr.And(pcs[4], cond), x_pcs[6]))
    # pc = 5 -> pc' = 0
    cfg.append(mgr.Implies(pcs[5], x_pcs[0]))
    # pc = 6 -> pc' = 0
    cfg.append(mgr.Implies(pcs[6], x_pcs[0]))
    # pc = 7 -> pc' = 0
    cfg.append(mgr.Implies(pcs[7], x_pcs[0]))
    # pc = -1 -> pc' = -1
    cfg.append(mgr.Implies(pcend, x_pcend))

    trans = []
    same = mgr.Equals(x_x, x)

    # pc = 0 -> same
    trans.append(mgr.Implies(pcs[0], same))
    # pc = 1 -> same
    trans.append(mgr.Implies(pcs[1], same))
    # pc = 2 -> same
    trans.append(mgr.Implies(pcs[2], same))
    # pc = 3 -> x' = -5
    trans.append(mgr.Implies(pcs[2], mgr.Equals(x_x, m_5)))
    # pc = 4 -> same
    trans.append(mgr.Implies(pcs[4], same))
    # pc = 5 -> x' = 35
    trans.append(mgr.Implies(pcs[5], mgr.Equals(x_x, ints[35])))
    # pc = 6 -> x' = x - 1
    trans.append(mgr.Implies(pcs[2], mgr.Equals(x_x, mgr.Minus(x, ints[1]))))
    # pc = 7 -> x' = 0
    trans.append(mgr.Implies(pcs[2], mgr.Equals(x_x, ints[0])))
    # pc = end -> same
    trans.append(mgr.Implies(pcend, same))

    trans = mgr.And(*cfg, *trans)

    fairness = mgr.Not(mgr.Equals(pc, m_1))

    return symbols, init, trans, fairness


def hints(env: PysmtEnv) -> FrozenSet[Hint]:
    assert isinstance(env, PysmtEnv)

    mgr = env.formula_manager
    pc = mgr.Symbol("pc", types.INT)
    x = mgr.Symbol("x", types.INT)
    symbs = frozenset([pc, x])

    m_6 = mgr.Int(-6)
    x_x = symb_to_next(mgr, x)
    loc = Location(env, mgr.Equals(x, m_6))
    loc.set_progress(0, mgr.Equals(x_x, x))
    h_x = Hint("h_x", env, frozenset([x]), symbs)
    h_x.set_locs([loc])

    return frozenset([h_x])
