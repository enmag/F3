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
    y = mgr.Symbol("y", types.INT)
    x_y = symb_to_next(mgr, y)
    old_x = mgr.Symbol("old_x", types.INT)
    x_old_x = symb_to_next(mgr, old_x)

    symbols = frozenset([pc, x, y, old_x])

    m_1 = mgr.Int(-1)

    n_locs = 4
    ints = [mgr.Int(idx) for idx in range(4)]
    pcs = []
    x_pcs = []
    for idx in range(n_locs):
        num = ints[idx]
        pcs.append(mgr.Equals(pc, num))
        x_pcs.append(mgr.Equals(x_pc, num))
    pcend = mgr.Equals(pc, m_1)
    x_pcend = mgr.Equals(x_pc, m_1)

    init = pcs[0]
    cfg = []
    # pc = 0 & TRUE -> pc' = 1
    cfg.append(mgr.Implies(mgr.And(pcs[0], mgr.TRUE()),
                           x_pcs[1]))
    # pc = 0 & !(TRUE) -> pc' = -1
    cfg.append(mgr.Implies(mgr.And(pcs[0], mgr.Not(mgr.TRUE())),
                           x_pcend))
    # pc = 1 -> pc' = 2
    cfg.append(mgr.Implies(pcs[1], x_pcs[2]))
    # pc = 2 -> pc' = 3
    cfg.append(mgr.Implies(pcs[2], x_pcs[3]))
    # pc = 3 -> pc' = 0
    cfg.append(mgr.Implies(pcs[3], x_pcs[0]))
    # pc = -1 -> pc' = -1
    cfg.append(mgr.Implies(pcend, x_pcend))

    trans = []
    same_x = mgr.Equals(x_x, x)
    same_y = mgr.Equals(x_y, y)
    same_old_x = mgr.Equals(x_old_x, old_x)
    same = mgr.And(same_x, same_y, same_old_x)
    # pc = 0 -> x' = x & y' = y & old_x' = old_x
    trans.append(mgr.Implies(pcs[0], same))
    # pc = 1 -> x' = x & y' = y & old_x' = x
    trans.append(mgr.Implies(pcs[1], mgr.And(same_x, same_y,
                                             mgr.Equals(x_old_x, x))))
    # pc = 2 -> x' = -y & y' = y & old_x' = old_x
    trans.append(mgr.Implies(pcs[2], mgr.And(mgr.Equals(x_x,
                                                        mgr.Times(m_1, y)),
                                             same_y, same_old_x)))
    # pc = 3 -> x' = x & y' = old_x & old_x' = old_x
    trans.append(mgr.Implies(pcs[3], mgr.And(same_x, mgr.Equals(x_y, old_x),
                                             same_old_x)))
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
    old_x = mgr.Symbol("old_x", types.INT)
    symbs = frozenset([pc, x, y, old_x])

    x_old_x = symb_to_next(mgr, old_x)
    stutter = mgr.Equals(x_old_x, old_x)
    l0 = Location(env, mgr.TRUE(), mgr.TRUE(), stutterT=stutter)
    l0.set_progress(0, mgr.Equals(x_old_x, x))
    h_old_x = Hint("h_old_x", env, frozenset([old_x]), symbs)
    h_old_x.set_locs([l0])

    x_y = symb_to_next(mgr, y)
    stutter = mgr.Equals(x_y, y)
    l0 = Location(env, mgr.TRUE(), mgr.TRUE(), stutterT=stutter)
    l0.set_progress(0, mgr.Equals(x_y, old_x))
    h_y = Hint("h_y", env, frozenset([y]), symbs)
    h_y.set_locs([l0])

    x_x = symb_to_next(mgr, x)
    m_1 = mgr.Int(-1)
    stutter = mgr.Equals(x_x, x)
    l0 = Location(env, mgr.TRUE(), mgr.TRUE(), stutterT=stutter)
    l0.set_progress(0, mgr.Equals(x_x, mgr.Times(m_1, y)))
    h_x = Hint("h_x", env, frozenset([x]), symbs)
    h_x.set_locs([l0])

    return frozenset([h_old_x, h_y, h_x])
