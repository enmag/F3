from typing import FrozenSet, Tuple
import pysmt.typing as types
from pysmt.environment import Environment as PysmtEnv
from pysmt.fnode import FNode
from utils import symb_to_next
from hint import Hint, Location


def transition_system(env: PysmtEnv) -> Tuple[FrozenSet[FNode], FNode, FNode,
                                              FNode]:
    assert isinstance(env, PysmtEnv)
    mgr = env.formula_manager
    pc = mgr.Symbol("pc", types.INT)
    x = mgr.Symbol("x", types.INT)
    y = mgr.Symbol("y", types.INT)
    z = mgr.Symbol("z", types.INT)
    x_pc = symb_to_next(mgr, pc)
    x_x = symb_to_next(mgr, x)
    x_y = symb_to_next(mgr, y)
    x_z = symb_to_next(mgr, z)
    symbols = frozenset([pc, x, y, z])

    n_locs = 5
    int_bound = n_locs
    pcs = []
    x_pcs = []
    ints = [mgr.Int(i) for i in range(int_bound)]

    for l in range(n_locs):
        n = ints[l]
        pcs.append(mgr.Equals(pc, n))
        x_pcs.append(mgr.Equals(x_pc, n))

    m_1 = mgr.Int(-1)
    pcend = mgr.Equals(pc, m_1)
    x_pcend = mgr.Equals(x_pc, m_1)

    # initial location.
    init = pcs[0]

    # control flow graph.
    cfg = mgr.And(
        # pc = -1 : -1,
        mgr.Implies(pcend, x_pcend),
        # pc = 0 & !(y >= 1) : -1,
        mgr.Implies(mgr.And(pcs[0], mgr.Not(mgr.GE(y, ints[1]))), x_pcend),
        # pc = 0 & y >= 1 : 1,
        mgr.Implies(mgr.And(pcs[0], mgr.GE(y, ints[1])), x_pcs[1]),
        # pc = 1 & !(z >= 1) : -1,
        mgr.Implies(mgr.And(pcs[1], mgr.Not(mgr.GE(z, ints[1]))), x_pcend),
        # pc = 1 & z >= 1 : 2,
        mgr.Implies(mgr.And(pcs[1], mgr.GE(z, ints[1])), x_pcs[2]),
        # pc = 2 & !(x >= 0) : -1,
        mgr.Implies(mgr.And(pcs[2], mgr.Not(mgr.GE(x, ints[0]))), x_pcend),
        # pc = 2 & x >= 0 : 3,
        mgr.Implies(mgr.And(pcs[2], mgr.GE(x, ints[0])), x_pcs[3]),
        # pc = 3 : 4,
        mgr.Implies(pcs[3], x_pcs[4]),
        # pc = 4 : 2,
        mgr.Implies(pcs[4], x_pcs[2]))

    # transition labels.
    labels = mgr.And(
        # (pc = -1 & pc' = -1) -> (x' = x & y' = y & z' = z),
        mgr.Implies(
            mgr.And(pcend, x_pcend),
            mgr.And(mgr.Equals(x_x, x), mgr.Equals(x_y, y),
                    mgr.Equals(x_z, z))),
        # (pc = 0 & pc' = -1) -> (x' = x & y' = y & z' = z),
        mgr.Implies(
            mgr.And(pcs[0], x_pcend),
            mgr.And(mgr.Equals(x_x, x), mgr.Equals(x_y, y),
                    mgr.Equals(x_z, z))),
        # (pc = 0 & pc' = 1)  -> (x' = x & y' = y & z' = z),
        mgr.Implies(
            mgr.And(pcs[0], x_pcs[1]),
            mgr.And(mgr.Equals(x_x, x), mgr.Equals(x_y, y),
                    mgr.Equals(x_z, z))),
        # (pc = 1 & pc' = -1) -> (x' = x & y' = y & z' = z),
        mgr.Implies(
            mgr.And(pcs[1], x_pcend),
            mgr.And(mgr.Equals(x_x, x), mgr.Equals(x_y, y),
                    mgr.Equals(x_z, z))),
        # (pc = 1 & pc' = 2)  -> (x' = x & y' = y & z' = z),
        mgr.Implies(
            mgr.And(pcs[1], x_pcs[2]),
            mgr.And(mgr.Equals(x_x, x), mgr.Equals(x_y, y),
                    mgr.Equals(x_z, z))),
        # (pc = 2 & pc' = -1) -> (x' = x & y' = y & z' = z),
        mgr.Implies(
            mgr.And(pcs[2], x_pcend),
            mgr.And(mgr.Equals(x_x, x), mgr.Equals(x_y, y),
                    mgr.Equals(x_z, z))),
        # (pc = 2 & pc' = 3)  -> (x' = x & y' = y & z' = z),
        mgr.Implies(
            mgr.And(pcs[2], x_pcs[3]),
            mgr.And(mgr.Equals(x_x, x), mgr.Equals(x_y, y),
                    mgr.Equals(x_z, z))),
        # (pc = 3 & pc' = 4)  -> (x' = y*z - 1 & y' = y & z' = z),
        mgr.Implies(
            mgr.And(pcs[3], x_pcs[4]),
            mgr.And(mgr.Equals(x_x, mgr.Minus(mgr.Times(y, z), ints[1])),
                    mgr.Equals(x_y, y), mgr.Equals(x_z, z))),
        # (pc = 4 & pc' = 2)  -> (x' = x & y' = y+1 & z' = z),
        mgr.Implies(
            mgr.And(pcs[4], x_pcs[2]),
            mgr.And(mgr.Equals(x_x, x), mgr.Equals(x_y, mgr.Plus(y, ints[1])),
                    mgr.Equals(x_z, z))))

    # transition relation.
    trans = mgr.And(cfg, labels)

    # fairness.
    fairness = mgr.Not(pcend)

    return symbols, init, trans, fairness


def hints(env: PysmtEnv) -> FrozenSet[Hint]:
    assert isinstance(env, PysmtEnv)

    mgr = env.formula_manager
    pc = mgr.Symbol("pc", types.INT)
    x = mgr.Symbol("x", types.INT)
    y = mgr.Symbol("y", types.INT)
    z = mgr.Symbol("z", types.INT)
    symbs = frozenset([pc, x, y, z])
    x_pc = symb_to_next(mgr, pc)
    x_x = symb_to_next(mgr, x)
    x_y = symb_to_next(mgr, y)
    x_z = symb_to_next(mgr, z)

    res = []

    i_0 = mgr.Int(0)
    i_1 = mgr.Int(1)
    i_2 = mgr.Int(2)
    i_3 = mgr.Int(3)

    stutter = mgr.Equals(x_y, y)
    loc = Location(env, mgr.TRUE(), mgr.LE(x, i_0), stutterT=stutter)
    loc.set_progress(0, mgr.Equals(x_y, mgr.Minus(y, i_1)))
    h_y = Hint("h_y0", env, frozenset([y]), symbs)
    h_y.set_locs([loc])
    res.append(h_y)


    loc = Location(env, mgr.LE(z, i_0))
    loc.set_progress(0, mgr.Equals(x_z, z))
    h_z = Hint("h_z0", env, frozenset([z]), symbs)
    h_z.set_locs([loc])
    res.append(h_z)


    stutter = mgr.Equals(x_y, y)
    loc0 = Location(env, mgr.GE(y, i_0))
    loc0.set_progress(1, mgr.Equals(x_y, mgr.Plus(y, i_1)))
    loc1 = Location(env, mgr.GE(y, i_1))
    loc1.set_progress(2, mgr.Equals(x_y, mgr.Plus(y, i_1)))
    loc2 = Location(env, mgr.GE(y, i_2))
    loc2.set_progress(0, mgr.Equals(x_y, y))
    h_y = Hint("h_y1", env, frozenset([y]), symbs)
    h_y.set_locs([loc0, loc1, loc2])
    res.append(h_y)


    stutter = mgr.Equals(x_x, x)
    loc = Location(env, mgr.GT(x, i_0), mgr.And(mgr.GT(y, i_1), mgr.GT(z, i_1)),
                   stutterT=stutter)
    loc.set_progress(0, mgr.GE(x_x, mgr.Minus(mgr.Times(y, z), i_2)))
    h_x = Hint("h_x1", env, frozenset([x]), symbs)
    h_x.set_locs([loc])
    res.append(h_x)


    loc0 = Location(env, mgr.GE(z, i_3))
    loc0.set_progress(0, mgr.GT(x_z, z))
    h_z = Hint("h_z1", env, frozenset([z]), symbs)
    h_z.set_locs([loc0])
    res.append(h_z)


    loc0 = Location(env, mgr.GE(z, i_3), mgr.GE(y, i_0))
    loc0.set_progress(1, mgr.GE(x_z, mgr.Plus(z, y)))
    loc1 = Location(env, mgr.GE(z, i_3), mgr.GE(x, i_0))
    loc1.set_progress(0, mgr.GE(x_z, mgr.Plus(z, i_0)))
    h_z = Hint("h_z2", env, frozenset([z]), symbs)
    h_z.set_locs([loc0, loc1])
    res.append(h_z)


    loc0 = Location(env, mgr.Equals(pc, i_1))
    loc0.set_progress(1, mgr.Equals(x_pc, i_3))
    loc1 = Location(env, mgr.Equals(pc, i_3))
    loc1.set_progress(0, mgr.Equals(x_pc, i_1))
    h_pc = Hint("h_pc2", env, frozenset([pc]), symbs)
    h_pc.set_locs([loc0, loc1])
    res.append(h_pc)


    loc0 = Location(env, mgr.GE(y, i_3))
    loc0.set_progress(1, mgr.Equals(x_y, mgr.Plus(y, i_1)))
    loc1 = Location(env, mgr.GE(y, i_3), mgr.GE(x, i_2))
    loc1.set_progress(0, mgr.Equals(x_y, mgr.Plus(y, x)))
    h_y = Hint("h_y3", env, frozenset([y]), symbs)
    h_y.set_locs([loc0, loc1])
    res.append(h_y)


    loc0 = Location(env, mgr.Equals(pc, i_2))
    loc0.set_progress(1, mgr.GT(x_pc, i_2))
    loc1 = Location(env, mgr.GE(pc, i_3))
    loc1.set_progress(0, mgr.Equals(x_pc, i_2))
    h_pc = Hint("h_pc3", env, frozenset([pc]), symbs)
    h_pc.set_locs([loc0, loc1])
    res.append(h_pc)


    loc0 = Location(env, mgr.GT(x, i_3), mgr.And(mgr.GT(y, i_1), mgr.GT(z, i_1)))
    loc0.set_progress(1, mgr.GE(x_x, mgr.Minus(mgr.Times(y, z), i_1)))
    loc1 = Location(env, mgr.GT(x, i_0), mgr.GE(y, i_1))
    loc1.set_progress(2, mgr.Equals(x_x, mgr.Plus(x, y)))
    loc2 = Location(env, mgr.GT(x, i_3))
    loc2.set_progress(2, mgr.Equals(x_x, x))
    h_x = Hint("h_x4", env, frozenset([x]), symbs)
    h_x.set_locs([loc0, loc1, loc2])
    res.append(h_x)


    loc0 = Location(env, mgr.GE(z, i_0))
    loc0.set_progress(1, mgr.Equals(x_z, z))
    loc1 = Location(env, mgr.GE(z, i_0))
    loc1.set_progress(0, mgr.Equals(x_z, mgr.Plus(z, i_3)))
    h_z = Hint("h_z4", env, frozenset([z]), symbs)
    h_z.set_locs([loc0, loc1])
    res.append(h_z)


    loc0 = Location(env, mgr.Equals(pc, i_2))
    loc0.set_progress(1, mgr.GT(x_pc, i_2))
    loc1 = Location(env, mgr.GE(pc, i_3))
    loc1.set_progress(2, mgr.GE(x_pc, i_3))
    loc2 = Location(env, mgr.GE(pc, i_3))
    loc2.set_progress(0, mgr.Equals(x_pc, i_2))
    h_pc = Hint("h_pc4", env, frozenset([pc]), symbs)
    h_pc.set_locs([loc0, loc1, loc2])
    res.append(h_pc)

    return frozenset(res)
