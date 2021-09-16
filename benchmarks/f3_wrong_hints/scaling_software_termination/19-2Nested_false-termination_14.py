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
    max_int = n_locs
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
    # pc = 1 -> x' = x + y & same_y
    trans.append(mgr.Implies(pcs[1],
                             mgr.And(mgr.Equals(x_x, mgr.Plus(x, y)),
                                     same_y)))
    # pc = 2 -> same_x & y' = y + 1
    trans.append(mgr.Implies(pcs[2],
                             mgr.And(same_x,
                                     mgr.Equals(x_y, mgr.Plus(y, ints[1])))))
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

    m_100 = mgr.Int(-100)
    m_1 = mgr.Int(-1)
    i_0 = mgr.Int(0)
    i_1 = mgr.Int(1)
    i_2 = mgr.Int(2)
    i_4 = mgr.Int(4)
    i_20 = mgr.Int(20)

    x_pc = symb_to_next(mgr, pc)
    x_x = symb_to_next(mgr, x)
    x_y = symb_to_next(mgr, y)
    res = []

    stutter = mgr.Equals(x_y, y)
    loc = Location(env, mgr.TRUE(), mgr.LE(x, i_20), stutterT=stutter)
    loc.set_progress(0, mgr.Equals(x_y, mgr.Plus(i_1, y)))
    h_y = Hint("h_y0", env, frozenset([y]), symbs)
    h_y.set_locs([loc])
    res.append(h_y)


    stutter = mgr.Equals(x_x, x)
    loc = Location(env, mgr.GE(x, i_20), mgr.GE(y, i_1), stutterT=stutter)
    loc.set_progress(0, mgr.Equals(x_x, mgr.Plus(x, y)))
    h_x = Hint("h_x0", env, frozenset([x]), symbs)
    h_x.set_locs([loc])
    res.append(h_x)


    stutter = mgr.Equals(x_y, y)
    loc = Location(env, mgr.TRUE(), mgr.LE(x, i_20), stutterT=stutter)
    loc.set_progress(0, mgr.Equals(x_y, mgr.Plus(x, y)))
    h_y = Hint("h_y1", env, frozenset([y]), symbs)
    h_y.set_locs([loc])
    res.append(h_y)


    stutter = mgr.Equals(x_x, x)
    loc = Location(env, mgr.GE(x, i_1), mgr.GE(y, i_1), stutterT=stutter)
    loc.set_progress(0, mgr.Equals(x_x, mgr.Plus(x, y)))
    h_x = Hint("h_x1", env, frozenset([x]), symbs)
    h_x.set_locs([loc])
    res.append(h_x)


    loc0 = Location(env, mgr.GE(y, m_100), mgr.LE(x, i_20))
    loc0.set_progress(1, mgr.Equals(x_y, mgr.Plus(x, y)))
    loc1 = Location(env, mgr.TRUE(), mgr.GE(x, m_100))
    loc1.set_progress(0, mgr.Equals(x_y, m_100))
    h_y = Hint("h_y2", env, frozenset([y]), symbs)
    h_y.set_locs([loc0, loc1])
    res.append(h_y)


    loc0 = Location(env, mgr.GE(y, m_100), mgr.LE(x, i_20))
    loc0.set_progress(1, mgr.Equals(x_y, mgr.Times(x, y)))
    loc1 = Location(env, mgr.TRUE(), mgr.GE(x, m_100))
    loc1.set_progress(0, mgr.Equals(x_y, m_100))
    h_y = Hint("h_y3", env, frozenset([y]), symbs)
    h_y.set_locs([loc0, loc1])
    res.append(h_y)


    loc0 = Location(env, mgr.GE(x, i_1), mgr.GE(y, i_1))
    loc0.set_progress(1, mgr.Equals(x_x, mgr.Times(x, y)))
    loc1 = Location(env, mgr.GE(x, i_1), mgr.GE(y, i_1))
    loc1.set_progress(0, mgr.Equals(x_x, y))
    h_x = Hint("h_x3", env, frozenset([x]), symbs)
    h_x.set_locs([loc0, loc1])
    res.append(h_x)


    loc0 = Location(env, mgr.Equals(pc, i_1))
    loc0.set_progress(1, mgr.GT(x_pc, mgr.Plus(pc, i_1)))
    loc1 = Location(env, mgr.GT(pc, i_2))
    loc1.set_progress(0, mgr.Equals(x_pc, i_1))
    h_pc = Hint("h_pc0", env, frozenset([pc]), symbs)
    h_pc.set_locs([loc0, loc1])
    res.append(h_pc)


    loc0 = Location(env, mgr.GE(y, m_100), mgr.LE(x, i_20))
    loc0.set_progress(1, mgr.Equals(x_y, mgr.Times(x, y)))
    loc1 = Location(env, mgr.TRUE(), mgr.GE(x, m_100))
    loc1.set_progress(2, mgr.GE(x_y, i_20))
    loc2 = Location(env, mgr.TRUE())
    loc2.set_progress(0, mgr.And(mgr.GE(x_y, m_100), mgr.LE(x_y, i_0)))
    h_y = Hint("h_y4", env, frozenset([y]), symbs)
    h_y.set_locs([loc0, loc1, loc2])
    res.append(h_y)


    loc0 = Location(env, mgr.GE(x, i_1), mgr.GE(y, i_1))
    loc0.set_progress(1, mgr.Equals(x_x, mgr.Times(x, y)))
    loc1 = Location(env, mgr.GE(x, i_1), mgr.GE(y, i_1))
    loc1.set_progress(2, mgr.GT(x_x, y))
    loc2 = Location(env, mgr.GE(x, i_2))
    loc2.set_progress(0, mgr.GE(x_x, i_20))
    h_x = Hint("h_x4", env, frozenset([x]), symbs)
    h_x.set_locs([loc0, loc1, loc2])
    res.append(h_x)


    loc0 = Location(env, mgr.TRUE())
    loc0.set_progress(0, mgr.TRUE())
    h_pc = Hint("h_pc1", env, frozenset([pc]), symbs)
    h_pc.set_locs([loc0])
    res.append(h_pc)


    loc0 = Location(env, mgr.GE(y, m_100))
    loc0.set_progress(0, mgr.Equals(x_y, mgr.Times(y, y)))
    h_y = Hint("h_y5", env, frozenset([y]), symbs)
    h_y.set_locs([loc0])
    res.append(h_y)


    loc0 = Location(env, mgr.LE(x, i_0))
    loc0.set_progress(1, mgr.Equals(x_x, mgr.Times(x, x)))
    loc1 = Location(env, mgr.GE(x, i_0))
    loc1.set_progress(0, mgr.LT(x_x, mgr.Times(m_1, x, x)))
    h_x = Hint("h_x5", env, frozenset([x]), symbs)
    h_x.set_locs([loc0, loc1])
    res.append(h_x)


    loc0 = Location(env, mgr.Equals(pc, i_1))
    loc0.set_progress(1, mgr.GT(x_pc, pc))
    loc1 = Location(env, mgr.GE(pc, i_2))
    loc1.set_progress(0, mgr.Equals(x_pc, mgr.Div(pc, pc)))
    h_pc = Hint("h_pc2", env, frozenset([pc]), symbs)
    h_pc.set_locs([loc0, loc1])
    res.append(h_pc)


    loc0 = Location(env, mgr.GE(y, m_100))
    loc0.set_progress(1, mgr.Equals(x_y, mgr.Times(y, y)))
    loc1 = Location(env, mgr.GE(y, i_0))
    loc1.set_progress(0, mgr.GE(x_y, mgr.Plus(y, i_1)))
    h_y = Hint("h_y6", env, frozenset([y]), symbs)
    h_y.set_locs([loc0, loc1])
    res.append(h_y)


    loc0 = Location(env, mgr.LE(x, i_20))
    loc0.set_progress(1, mgr.Equals(x_x, mgr.Plus(mgr.Times(x, x), i_1)))
    loc1 = Location(env, mgr.GE(x, i_20))
    loc1.set_progress(0, mgr.LT(x_x, mgr.Times(m_1, x, x)))
    h_x = Hint("h_x6", env, frozenset([x]), symbs)
    h_x.set_locs([loc0, loc1])
    res.append(h_x)


    loc0 = Location(env, mgr.LE(pc, i_1))
    loc0.set_progress(1, mgr.GT(x_pc, pc))
    loc1 = Location(env, mgr.LE(pc, i_2))
    loc1.set_progress(0, mgr.Equals(x_pc, mgr.Div(pc, pc)))
    h_pc = Hint("h_pc3", env, frozenset([pc]), symbs)
    h_pc.set_locs([loc0, loc1])
    res.append(h_pc)


    loc0 = Location(env, mgr.GE(y, i_0), mgr.GE(pc, i_1))
    loc0.set_progress(1, mgr.Equals(x_y, mgr.Plus(y, pc)))
    loc1 = Location(env, mgr.GE(y, i_1))
    loc1.set_progress(0, mgr.Equals(x_y, y))
    h_y = Hint("h_y7", env, frozenset([y]), symbs)
    h_y.set_locs([loc0, loc1])
    res.append(h_y)


    loc0 = Location(env, mgr.GE(x, i_1), mgr.GT(y, i_1))
    loc0.set_progress(1, mgr.Equals(x_x, mgr.Plus(mgr.Times(x, y), i_1)))
    loc1 = Location(env, mgr.GE(x, i_2))
    loc1.set_progress(2, mgr.LT(x_x, mgr.Times(m_1, x, x)))
    loc2 = Location(env, mgr.LE(x, i_4))
    loc2.set_progress(0, mgr.GE(x_x, mgr.Div(x, x)))
    h_x = Hint("h_x7", env, frozenset([x]), symbs)
    h_x.set_locs([loc0, loc1, loc2])
    res.append(h_x)

    return frozenset(res)
