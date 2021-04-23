from pysmt.environment import Environment as PysmtEnv
from pysmt.fnode import FNode
import pysmt.typing as types

from utils import symb_to_next


def transition_system(env: PysmtEnv) -> (frozenset, FNode, FNode, FNode):
    assert isinstance(env, PysmtEnv)
    mgr = env.formula_manager
    a = mgr.Symbol("a", types.INT)
    b = mgr.Symbol("b", types.INT)
    pc = mgr.Symbol("pc", types.INT)
    x = mgr.Symbol("x", types.INT)
    y = mgr.Symbol("y", types.INT)
    z = mgr.Symbol("z", types.INT)
    x_a = symb_to_next(mgr, a)
    x_b = symb_to_next(mgr, b)
    x_pc = symb_to_next(mgr, pc)
    x_x = symb_to_next(mgr, x)
    x_y = symb_to_next(mgr, y)
    x_z = symb_to_next(mgr, z)
    symbols = frozenset([a, b, pc, x, y, z])

    n_locs = 10
    int_bound = 43
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

    # initial location.
    init = pcs[0]

    # control flow graph.
    cfg = mgr.And(
        # pc = -1 : -1,
        mgr.Implies(pcend, x_pcend),
        # pc = 0 & !(x >= 1) : -1,
        mgr.Implies(mgr.And(pcs[0], mgr.Not(mgr.GE(x, ints[1]))), x_pcend),
        # pc = 0 & x >= 1 : 1,
        mgr.Implies(mgr.And(pcs[0], mgr.GE(x, ints[1])),
                    mgr.Equals(x_pc, ints[1])),
        # pc = 1 & !(b < 0) : -1,
        mgr.Implies(mgr.And(pcs[1], mgr.Not(mgr.LT(b, ints[0]))), x_pcend),
        # pc = 1 & b < 0 : 2,
        mgr.Implies(mgr.And(pcs[1], mgr.LT(b, ints[0])),
                    mgr.Equals(x_pc, ints[2])),
        # pc = 2 & !(a >= 0) : -1,
        mgr.Implies(mgr.And(pcs[2], mgr.Not(mgr.GE(a, ints[0]))), x_pcend),
        # pc = 2 & a >= 0 : 3,
        mgr.Implies(mgr.And(pcs[2], mgr.GE(a, ints[0])),
                    mgr.Equals(x_pc, ints[3])),
        # pc = 3 & !(x >= y & z < 42) : -1,
        mgr.Implies(mgr.And(pcs[3], mgr.Not(mgr.And(mgr.GE(x, y),
                                                    mgr.LT(z, ints[42])))),
                    x_pcend),
        # pc = 3 & (x >= y & z < 42) : 4,
        mgr.Implies(mgr.And(pcs[3], mgr.GE(x, y), mgr.LT(z, ints[42])),
                    mgr.Equals(x_pc, ints[4])),
        # pc = 4 : {5, 7},
        mgr.Implies(pcs[4],
                    mgr.Or(mgr.Equals(x_pc, ints[5]),
                           mgr.Equals(x_pc, ints[7]))),
        # pc = 5 : 6,
        mgr.Implies(pcs[5], mgr.Equals(x_pc, ints[6])),
        # pc = 6 : 3,
        mgr.Implies(pcs[6], mgr.Equals(x_pc, ints[3])),
        # pc = 7 : 8,
        mgr.Implies(pcs[7], mgr.Equals(x_pc, ints[8])),
        # pc = 8 : 9,
        mgr.Implies(pcs[8], x_pcs[9]),
        # pc = 9 : 3,
        mgr.Implies(pcs[9], mgr.Equals(x_pc, ints[3]))
    )

    # transition labels.
    labels = mgr.And(
        # (pc = -1 & pc' = -1) -> (a' = a & b' = b & x' = x & y' = y & z' = z),
        mgr.Implies(mgr.And(pcend, x_pcend),
                    mgr.And(mgr.Equals(x_a, a), mgr.Equals(x_b, b),
                            mgr.Equals(x_x, x),
                            mgr.Equals(x_y, y), mgr.Equals(x_z, z))),
        # (pc = 0 & pc' = -1) -> (a' = a & b' = b & x' = x & y' = y & z' = z),
        mgr.Implies(mgr.And(pcs[0], x_pcend),
                    mgr.And(mgr.Equals(x_a, a),
                            mgr.Equals(x_b, b), mgr.Equals(x_x, x),
                            mgr.Equals(x_y, y), mgr.Equals(x_z, z))),
        # (pc = 0 & pc' = 1)  -> (a' = a & b' = b & x' = x & y' = y & z' = z),
        mgr.Implies(mgr.And(pcs[0], mgr.Equals(x_pc, ints[1])),
                    mgr.And(mgr.Equals(x_a, a), mgr.Equals(x_b, b),
                            mgr.Equals(x_x, x),
                            mgr.Equals(x_y, y), mgr.Equals(x_z, z))),
        # (pc = 1 & pc' = -1) -> (a' = a & b' = b & x' = x & y' = y & z' = z),
        mgr.Implies(mgr.And(pcs[1], x_pcend),
                    mgr.And(mgr.Equals(x_a, a), mgr.Equals(x_b, b),
                            mgr.Equals(x_x, x),
                            mgr.Equals(x_y, y), mgr.Equals(x_z, z))),
        # (pc = 1 & pc' = 2)  -> (a' = a & b' = b & x' = x & y' = y & z' = z),
        mgr.Implies(mgr.And(pcs[1], mgr.Equals(x_pc, ints[2])),
                    mgr.And(mgr.Equals(x_a, a), mgr.Equals(x_b, b),
                            mgr.Equals(x_x, x),
                            mgr.Equals(x_y, y), mgr.Equals(x_z, z))),
        # (pc = 2 & pc' = -1) -> (a' = a & b' = b & x' = x & y' = y & z' = z),
        mgr.Implies(mgr.And(pcs[2], x_pcend),
                    mgr.And(mgr.Equals(x_a, a), mgr.Equals(x_b, b),
                            mgr.Equals(x_x, x),
                            mgr.Equals(x_y, y), mgr.Equals(x_z, z))),
        # (pc = 2 & pc' = 3)  -> (a' = a & b' = b & x' = x & y' = y & z' = z),
        mgr.Implies(mgr.And(pcs[2], mgr.Equals(x_pc, ints[3])),
                    mgr.And(mgr.Equals(x_a, a), mgr.Equals(x_b, b),
                            mgr.Equals(x_x, x),
                            mgr.Equals(x_y, y), mgr.Equals(x_z, z))),
        # (pc = 3 & pc' = -1) -> (a' = a & b' = b & x' = x & y' = y & z' = z),
        mgr.Implies(mgr.And(pcs[3], x_pcend),
                    mgr.And(mgr.Equals(x_a, a), mgr.Equals(x_b, b),
                            mgr.Equals(x_x, x),
                            mgr.Equals(x_y, y), mgr.Equals(x_z, z))),
        # (pc = 3 & pc' = 4)  -> (a' = a & b' = b & x' = x & y' = y & z' = z),
        mgr.Implies(mgr.And(pcs[3], mgr.Equals(x_pc, ints[4])),
                    mgr.And(mgr.Equals(x_a, a), mgr.Equals(x_b, b),
                            mgr.Equals(x_x, x),
                            mgr.Equals(x_y, y), mgr.Equals(x_z, z))),
        # (pc = 4 & pc' = 5)  -> (a' = a & b' = b & x' = x & y' = y & z' = z),
        mgr.Implies(mgr.And(pcs[4], mgr.Equals(x_pc, ints[5])),
                    mgr.And(mgr.Equals(x_a, a), mgr.Equals(x_b, b),
                            mgr.Equals(x_x, x),
                            mgr.Equals(x_y, y), mgr.Equals(x_z, z))),
        # (pc = 4 & pc' = 7)  -> (a' = a & b' = b & x' = x & y' = y & z' = z),
        mgr.Implies(mgr.And(pcs[4], mgr.Equals(x_pc, ints[7])),
                    mgr.And(mgr.Equals(x_a, a), mgr.Equals(x_b, b),
                            mgr.Equals(x_x, x),
                            mgr.Equals(x_y, y), mgr.Equals(x_z, z))),
        # (pc = 5 & pc' = 6)  -> (a' = a & b' = b & x' = 1 & y' = y & z' = z),
        mgr.Implies(mgr.And(pcs[5], mgr.Equals(x_pc, ints[6])),
                    mgr.And(mgr.Equals(x_a, a), mgr.Equals(x_b, b),
                            mgr.Equals(x_x, ints[1]),
                            mgr.Equals(x_y, y), mgr.Equals(x_z, z))),
        # (pc = 6 & pc' = 3)  -> (a' = a & b' = b & x' = x & y' = 15 & z' = z),
        mgr.Implies(mgr.And(pcs[6], mgr.Equals(x_pc, ints[3])),
                    mgr.And(mgr.Equals(x_a, a), mgr.Equals(x_b, b),
                            mgr.Equals(x_x, x),
                            mgr.Equals(x_y, ints[15]), mgr.Equals(x_z, z))),
        # (pc = 7 & pc' = 8)  -> (a' = a & b' = b &           y' = y & z' = z),
        mgr.Implies(mgr.And(pcs[7], mgr.Equals(x_pc, ints[8])),
                    mgr.And(mgr.Equals(x_a, a), mgr.Equals(x_b, b),
                            mgr.Equals(x_y, y),
                            mgr.Equals(x_z, z))),
        # (pc = 8 & pc' = 9)  -> (a' = a & b' = b & x' = x & y' = y & z' = a*b),
        mgr.Implies(mgr.And(pcs[8], x_pcs[9]),
                    mgr.And(mgr.Equals(x_a, a), mgr.Equals(x_b, b),
                            mgr.Equals(x_x, x),
                            mgr.Equals(x_y, y),
                            mgr.Equals(x_z, mgr.Times(a, b)))),
        # (pc = 9 & pc' = 3)  -> (a' = a+1 & b' = b & x' = x & y' = y & z' = z),
        mgr.Implies(mgr.And(pcs[9], mgr.Equals(x_pc, ints[3])),
                    mgr.And(mgr.Equals(x_a, mgr.Plus(a, ints[1])),
                            mgr.Equals(x_b, b),
                            mgr.Equals(x_x, x), mgr.Equals(x_y, y),
                            mgr.Equals(x_z, z)))
    )

    # transition relation.
    trans = mgr.And(cfg, labels)

    # fairness.
    fairness = mgr.Not(pcend)

    return symbols, init, trans, fairness
