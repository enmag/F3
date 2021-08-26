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
    y = mgr.Symbol("y", types.INT)
    x_pc = symb_to_next(mgr, pc)
    x_x = symb_to_next(mgr, x)
    x_y = symb_to_next(mgr, y)

    symbols = frozenset([pc, x, y])

    m_1 = mgr.Int(-1)

    n_locs = 3
    max_int = 4
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

    init = mgr.And(pcs[0], mgr.Equals(x, ints[1]), mgr.Equals(y, ints[1]))

    cfg = []
    # pc = 0 & (x >= 0) -> pc' = 1
    cond = mgr.GE(x, ints[0])
    cfg.append(mgr.Implies(mgr.And(pcs[0], cond), x_pcs[1]))
    # pc = 0 & !(x >= 0) -> pc' = -1
    cfg.append(mgr.Implies(mgr.And(pcs[0], mgr.Not(cond)), x_pcend))
    # pc = 1 -> pc' = 2
    cfg.append(mgr.Implies(pcs[1], x_pcs[2]))
    # pc = 2 -> pc' = 0
    cfg.append(mgr.Implies(pcs[2], x_pcs[0]))
    # pc = -1 -> pc' = -1
    cfg.append(mgr.Implies(pcend, x_pcend))

    trans = []
    same_x = mgr.Equals(x_x, x)
    same_y = mgr.Equals(x_y, y)
    same = mgr.And(same_x, same_y)

    # pc = 0 -> same
    trans.append(mgr.Implies(pcs[0], same))
    # pc = 1 -> x' = 2x & same_y
    trans.append(mgr.Implies(pcs[1],
                             mgr.And(mgr.Equals(x_x, mgr.Times(ints[2], x)),
                                     same_y)))
    # pc = 2 -> same_x & y' = 3y
    trans.append(mgr.Implies(pcs[2],
                             mgr.And(same_x,
                                     mgr.Equals(x_y, mgr.Times(ints[3], y)))))
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
    y = mgr.Symbol("y", types.INT)
    symbs = frozenset([pc, x, y])

    i_0 = mgr.Int(0)
    i_2 = mgr.Int(2)
    i_3 = mgr.Int(3)

    x_x = symb_to_next(mgr, x)
    stutter = mgr.Equals(x_x, x)
    loc = Location(env, mgr.GE(x, i_0), stutterT=stutter)
    loc.set_progress(0, mgr.Equals(x_x, mgr.Times(i_2, x)))
    h_x = Hint("h_x", env, frozenset([x]), symbs)
    h_x.set_locs([loc])

    x_y = symb_to_next(mgr, y)
    stutter = mgr.Equals(x_y, y)
    loc = Location(env, mgr.GE(y, i_0), stutterT=stutter)
    loc.set_progress(0, mgr.Equals(x_y, mgr.Times(i_3, y)))
    h_y = Hint("h_y", env, frozenset([y]), symbs)
    h_y.set_locs([loc])

    return frozenset([h_x, h_y])