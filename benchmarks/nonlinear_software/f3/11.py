from pysmt.environment import Environment as PysmtEnv
from pysmt.fnode import FNode
import pysmt.typing as types

from utils import symb_to_next


def transition_system(env: PysmtEnv) -> (frozenset, FNode, FNode, FNode):
    assert isinstance(env, PysmtEnv)
    mgr = env.formula_manager
    pc = mgr.Symbol("pc", types.INT)
    w = mgr.Symbol("w", types.INT)
    x = mgr.Symbol("x", types.INT)
    y = mgr.Symbol("y", types.INT)
    z = mgr.Symbol("z", types.INT)
    x_pc = symb_to_next(mgr, pc)
    x_w = symb_to_next(mgr, w)
    x_x = symb_to_next(mgr, x)
    x_y = symb_to_next(mgr, y)
    x_z = symb_to_next(mgr, z)
    symbols = frozenset([pc, w, x, y, z])

    n_locs = 7
    int_bound = n_locs
    pcs = []
    x_pcs = []
    ints = []

    for l in range(n_locs):
        n = mgr.Int(l)
        ints.append(n)
        pcs.append(mgr.Equals(pc, n))
        x_pcs.append(mgr.Equals(x_pc, n))

    for l in range(n_locs, int_bound):
        ints.append(mgr.Int(l))

    m_1 = mgr.Int(-1)
    pcend = mgr.Equals(pc, m_1)
    x_pcend = mgr.Equals(x_pc, m_1)

    m_5 = mgr.Int(-5)

    # initial location.
    init = pcs[0]

    # control flow graph.
    cfg = mgr.And(
        # pc = -1 : -1,
        mgr.Implies(pcend, x_pcend),
        # pc = 0 & !(z >= 5) : -1,
        mgr.Implies(mgr.And(pcs[0], mgr.Not(mgr.GE(z, ints[5]))),
                    x_pcend),
        # pc = 0 & z >= 5 : 1,
        mgr.Implies(mgr.And(pcs[0], mgr.GE(z, ints[5])), x_pcs[1]),
        # pc = 1 & !(y <= 2) : -1,
        mgr.Implies(mgr.And(pcs[1], mgr.Not(mgr.LE(y, ints[2]))),
                    x_pcend),
        # pc = 1 & y <= 2 : 2,
        mgr.Implies(mgr.And(pcs[1], mgr.LE(y, ints[2])), x_pcs[2]),
        # pc = 2 & !(w <= -5) : -1,
        mgr.Implies(mgr.And(pcs[2], mgr.Not(mgr.LE(w, m_5))),
                    x_pcend),
        # pc = 2 & w <= -5 : 3,
        mgr.Implies(mgr.And(pcs[2], mgr.LE(w, m_5)), x_pcs[3]),
        # pc = 3 & !(x >= y) : -1,
        mgr.Implies(mgr.And(pcs[3], mgr.Not(mgr.GE(x, y))),
                    x_pcend),
        # pc = 3 & (x >= y) : 4,
        mgr.Implies(mgr.And(pcs[3], mgr.GE(x, y)),
                    x_pcs[4]),
        # pc = 4 : 5,
        mgr.Implies(pcs[4], x_pcs[5]),
        # pc = 5 : 6,
        mgr.Implies(pcs[5], x_pcs[6]),
        # pc = 6 : 3,
        mgr.Implies(pcs[6], x_pcs[3])
    )

    # transition labels.
    labels = mgr.And(
        # (pc = -1 & pc' = -1) -> (w' = w & x' = x & y' = y & z' = z),
        mgr.Implies(mgr.And(pcend, x_pcend),
                    mgr.And(mgr.Equals(x_w, w), mgr.Equals(x_x, x),
                            mgr.Equals(x_y, y), mgr.Equals(x_z, z))),
        # (pc = 0 & pc' = -1) -> (w' = w & x' = x & y' = y & z' = z),
        mgr.Implies(mgr.And(pcs[0], x_pcend),
                    mgr.And(mgr.Equals(x_w, w), mgr.Equals(x_x, x),
                            mgr.Equals(x_y, y), mgr.Equals(x_z, z))),
        # (pc = 0 & pc' = 1)  -> (w' = w & x' = x & y' = y & z' = z),
        mgr.Implies(mgr.And(pcs[0], x_pcs[1]),
                    mgr.And(mgr.Equals(x_w, w), mgr.Equals(x_x, x),
                            mgr.Equals(x_y, y), mgr.Equals(x_z, z))),
        # (pc = 1 & pc' = -1) -> (w' = w & x' = x & y' = y & z' = z),
        mgr.Implies(mgr.And(pcs[1], x_pcend),
                    mgr.And(mgr.Equals(x_w, w), mgr.Equals(x_x, x),
                            mgr.Equals(x_y, y), mgr.Equals(x_z, z))),
        # (pc = 1 & pc' = 2)  -> (w' = w & x' = x & y' = y & z' = z),
        mgr.Implies(mgr.And(pcs[1], x_pcs[2]),
                    mgr.And(mgr.Equals(x_w, w), mgr.Equals(x_x, x),
                            mgr.Equals(x_y, y), mgr.Equals(x_z, z))),
        # (pc = 2 & pc' = -1) -> (w' = w & x' = x & y' = y & z' = z),
        mgr.Implies(mgr.And(pcs[2], x_pcend),
                    mgr.And(mgr.Equals(x_w, w), mgr.Equals(x_x, x),
                            mgr.Equals(x_y, y), mgr.Equals(x_z, z))),
        # (pc = 2 & pc' = 3)  -> (w' = w & x' = x & y' = y & z' = z),
        mgr.Implies(mgr.And(pcs[2], x_pcs[3]),
                    mgr.And(mgr.Equals(x_w, w), mgr.Equals(x_x, x),
                            mgr.Equals(x_y, y), mgr.Equals(x_z, z))),
        # (pc = 3 & pc' = -1) -> (w' = w & x' = x & y' = y & z' = z),
        mgr.Implies(mgr.And(pcs[3], x_pcend),
                    mgr.And(mgr.Equals(x_w, w), mgr.Equals(x_x, x),
                            mgr.Equals(x_y, y), mgr.Equals(x_z, z))),
        # (pc = 3 & pc' = 4)  -> (w' = w & x' = x & y' = y & z' = z),
        mgr.Implies(mgr.And(pcs[3], x_pcs[4]),
                    mgr.And(mgr.Equals(x_w, w), mgr.Equals(x_x, x),
                            mgr.Equals(x_y, y), mgr.Equals(x_z, z))),
        # (pc = 4 & pc' = 5)  -> (w' = w & x' = -z*w & y' = y & z' = z),
        mgr.Implies(mgr.And(pcs[4], x_pcs[5]),
                    mgr.And(mgr.Equals(x_w, w),
                            mgr.Equals(x_x, mgr.Times(m_1, z, w)),
                            mgr.Equals(x_y, y), mgr.Equals(x_z, z))),
        # (pc = 5 & pc' = 6)  -> (w' = w & x' = x & y' = y & z' = z+1),
        mgr.Implies(mgr.And(pcs[5], x_pcs[6]),
                    mgr.And(mgr.Equals(x_w, w), mgr.Equals(x_x, x),
                            mgr.Equals(x_y, y),
                            mgr.Equals(x_z, mgr.Plus(z, ints[1])))),
        # (pc = 6 & pc' = 3)  -> (w' = w-1 & x' = x & y' = y & z' = z),
        mgr.Implies(mgr.And(pcs[6], x_pcs[3]),
                    mgr.And(mgr.Equals(x_w, mgr.Minus(w, ints[1])),
                            mgr.Equals(x_x, x),
                            mgr.Equals(x_y, y), mgr.Equals(x_z, z)))
    )

    # transition relation.
    trans = mgr.And(cfg, labels)

    # fairness.
    fairness = mgr.Not(pcend)

    return symbols, init, trans, fairness
