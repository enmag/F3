import pysmt.typing as types
from typing import Tuple, FrozenSet
from pysmt.environment import Environment as PysmtEnv
from pysmt.fnode import FNode
from expr_utils import symb2next


def transition_system(env: PysmtEnv) -> Tuple[FrozenSet[FNode], FNode, FNode, FNode]:
    assert isinstance(env, PysmtEnv)
    mgr = env.formula_manager
    pc = mgr.Symbol("pc", types.INT)
    w = mgr.Symbol("w", types.INT)
    x = mgr.Symbol("x", types.INT)
    y = mgr.Symbol("y", types.INT)
    z = mgr.Symbol("z", types.INT)
    x_pc = symb2next(env, pc)
    x_w = symb2next(env, w)
    x_x = symb2next(env, x)
    x_y = symb2next(env, y)
    x_z = symb2next(env, z)
    symbols = frozenset([pc, w, x, y, z])

    n_locs = 17
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

    m_5 = mgr.Int(-5)

    # initial location.
    init = pcs[0]

    # control flow graph.
    cfg = mgr.And(
        # pc = -1 : -1,
        mgr.Implies(pcend, x_pcend),
        # pc = 0 & !(z >= 3) : -1,
        mgr.Implies(mgr.And(pcs[0], mgr.Not(mgr.GE(z, ints[3]))), x_pcend),
        # pc = 0 & z >= 3 : 1,
        mgr.Implies(mgr.And(pcs[0], mgr.GE(z, ints[3])), x_pcs[1]),
        # pc = 1 & !( y >= 2) : -1,
        mgr.Implies(mgr.And(pcs[1], mgr.Not(mgr.GE(y, ints[2]))), x_pcend),
        # pc = 1 & y >= 2 : 2,
        mgr.Implies(mgr.And(pcs[1], mgr.GE(y, ints[2])), x_pcs[2]),
        # pc = 2 : {3, 5},
        mgr.Implies(pcs[2], mgr.Or(x_pcs[3], x_pcs[5])),
        # pc = 3 & !(z < -5) : -1,
        mgr.Implies(mgr.And(pcs[3], mgr.Not(mgr.LT(z, m_5))), x_pcend),
        # pc = 3 & z < -5 : 4,
        mgr.Implies(mgr.And(pcs[3], mgr.LT(z, m_5)), x_pcs[4]),
        # pc = 4 : -1,
        mgr.Implies(pcs[4], x_pcend),
        # pc = 5 & !(w >= 2) : 13,
        mgr.Implies(mgr.And(pcs[5], mgr.Not(mgr.GE(w, ints[2]))), x_pcs[13]),
        # pc = 5 & w >= 2 : 6,
        mgr.Implies(mgr.And(pcs[5], mgr.GE(w, ints[2])), x_pcs[6]),
        # pc = 6 : {7, 9},
        mgr.Implies(pcs[6], mgr.Or(x_pcs[7], x_pcs[9])),
        # pc = 7 & !(z < -5) : -1,
        mgr.Implies(mgr.And(pcs[7], mgr.Not(mgr.LT(z, m_5))), x_pcend),
        # pc = 7 & z < -5 : 8,
        mgr.Implies(mgr.And(pcs[7], mgr.LT(z, m_5)), x_pcs[8]),
        # pc = 8 : -1,
        mgr.Implies(pcs[8], x_pcend),
        # pc = 9 & !(x >= 0) : 5,
        mgr.Implies(mgr.And(pcs[9], mgr.Not(mgr.GE(x, ints[0]))), x_pcs[5]),
        # pc = 9 & x >= 0 : 10,
        mgr.Implies(mgr.And(pcs[9], mgr.GE(x, ints[0])), x_pcs[10]),
        # pc = 10 : 11,
        mgr.Implies(pcs[10], x_pcs[11]),
        # pc = 11 : 12,
        mgr.Implies(pcs[11], x_pcs[12]),
        # pc = 12 : 9,
        mgr.Implies(pcs[12], x_pcs[9]),
        # pc = 13 : {-1, 14},
        mgr.Implies(pcs[13], mgr.Or(x_pcend, x_pcs[14])),
        # pc = 14 & !(z < -5) : -1,
        mgr.Implies(mgr.And(pcs[14], mgr.Not(mgr.LT(z, m_5))), x_pcend),
        # pc = 14 & (z < -5) : 15,
        mgr.Implies(mgr.And(pcs[14], mgr.LT(z, m_5)), x_pcs[15]),
        # pc = 15 : -1,
        mgr.Implies(pcs[15], x_pcend)
    )

    # transition labels.
    labels = mgr.And(
        # (pc = -1 & pc' = -1) -> (w' = w & x' = x & y' = y & z' = z),
        mgr.Implies(mgr.And(pcend, x_pcend),
                    mgr.And(mgr.Equals(x_w, w), mgr.Equals(x_x, x),
                            mgr.Equals(x_y, y), mgr.Equals(x_z, z))),
        # (pc = 0 & pc' = -1)  -> (w' = w & x' = x & y' = y & z' = z),
        mgr.Implies(mgr.And(pcs[0], x_pcend),
                    mgr.And(mgr.Equals(x_w, w), mgr.Equals(x_x, x),
                            mgr.Equals(x_y, y), mgr.Equals(x_z, z))),
        # (pc = 0 & pc' = 1)   -> (w' = w & x' = x & y' = y & z' = z),
        mgr.Implies(mgr.And(pcs[0], x_pcs[1]),
                    mgr.And(mgr.Equals(x_w, w), mgr.Equals(x_x, x),
                            mgr.Equals(x_y, y), mgr.Equals(x_z, z))),
        # (pc = 1 & pc' = -1)  -> (w' = w & x' = x & y' = y & z' = z),
        mgr.Implies(mgr.And(pcs[1], x_pcend),
                    mgr.And(mgr.Equals(x_w, w), mgr.Equals(x_x, x),
                            mgr.Equals(x_y, y), mgr.Equals(x_z, z))),
        # (pc = 1 & pc' = 2)   -> (w' = w & x' = x & y' = y & z' = z),
        mgr.Implies(mgr.And(pcs[1], x_pcs[2]),
                    mgr.And(mgr.Equals(x_w, w), mgr.Equals(x_x, x),
                            mgr.Equals(x_y, y), mgr.Equals(x_z, z))),
        # (pc = 2 & pc' = 3)   -> (w' = w & x' = x & y' = y & z' = z),
        mgr.Implies(mgr.And(pcs[2], x_pcs[3]),
                    mgr.And(mgr.Equals(x_w, w), mgr.Equals(x_x, x),
                            mgr.Equals(x_y, y), mgr.Equals(x_z, z))),
        # (pc = 2 & pc' = 5)   -> (w' = w & x' = x & y' = y & z' = z),
        mgr.Implies(mgr.And(pcs[2], x_pcs[5]),
                    mgr.And(mgr.Equals(x_w, w), mgr.Equals(x_x, x),
                            mgr.Equals(x_y, y), mgr.Equals(x_z, z))),
        # (pc = 3 & pc' = -1)  -> (w' = w & x' = x & y' = y & z' = z),
        mgr.Implies(mgr.And(pcs[3], x_pcend),
                    mgr.And(mgr.Equals(x_w, w), mgr.Equals(x_x, x),
                            mgr.Equals(x_y, y), mgr.Equals(x_z, z))),
        # (pc = 3 & pc' = 4)   -> (w' = w & x' = x & y' = y & z' = z),
        mgr.Implies(mgr.And(pcs[3], x_pcs[4]),
                    mgr.And(mgr.Equals(x_w, w), mgr.Equals(x_x, x),
                            mgr.Equals(x_y, y), mgr.Equals(x_z, z))),
        # (pc = 4 & pc' = -1)  -> (w' = w & x' = x & y' = y & z' = z),
        mgr.Implies(mgr.And(pcs[4], x_pcend),
                    mgr.And(mgr.Equals(x_w, w), mgr.Equals(x_x, x),
                            mgr.Equals(x_y, y), mgr.Equals(x_z, z))),
        # (pc = 5 & pc' = 13)  -> (w' = w & x' = x & y' = y & z' = z),
        mgr.Implies(mgr.And(pcs[5], x_pcs[13]),
                    mgr.And(mgr.Equals(x_w, w), mgr.Equals(x_x, x),
                            mgr.Equals(x_y, y), mgr.Equals(x_z, z))),
        # (pc = 5 & pc' = 6)   -> (w' = w & x' = x & y' = y & z' = z),
        mgr.Implies(mgr.And(pcs[5], x_pcs[6]),
                    mgr.And(mgr.Equals(x_w, w), mgr.Equals(x_x, x),
                            mgr.Equals(x_y, y), mgr.Equals(x_z, z))),
        # (pc = 6 & pc' = 7)   -> (w' = w & x' = x & y' = y & z' = z),
        mgr.Implies(mgr.And(pcs[6], x_pcs[7]),
                    mgr.And(mgr.Equals(x_w, w), mgr.Equals(x_x, x),
                            mgr.Equals(x_y, y), mgr.Equals(x_z, z))),
        # (pc = 6 & pc' = 9)   -> (w' = w & x' = x & y' = y & z' = z),
        mgr.Implies(mgr.And(pcs[6], x_pcs[9]),
                    mgr.And(mgr.Equals(x_w, w), mgr.Equals(x_x, x),
                            mgr.Equals(x_y, y), mgr.Equals(x_z, z))),
        # (pc = 7 & pc' = -1)  -> (w' = w & x' = x & y' = y & z' = z),
        mgr.Implies(mgr.And(pcs[7], x_pcend),
                    mgr.And(mgr.Equals(x_w, w), mgr.Equals(x_x, x),
                            mgr.Equals(x_y, y), mgr.Equals(x_z, z))),
        # (pc = 7 & pc' = 8)   -> (w' = w & x' = x & y' = y & z' = z),
        mgr.Implies(mgr.And(pcs[7], x_pcs[8]),
                    mgr.And(mgr.Equals(x_w, w), mgr.Equals(x_x, x),
                            mgr.Equals(x_y, y), mgr.Equals(x_z, z))),
        # (pc = 8 & pc' = -1)  -> (w' = w & x' = x & y' = y & z' = z),
        mgr.Implies(mgr.And(pcs[8], x_pcend),
                    mgr.And(mgr.Equals(x_w, w), mgr.Equals(x_x, x),
                            mgr.Equals(x_y, y), mgr.Equals(x_z, z))),
        # (pc = 9 & pc' = 5)   -> (w' = w & x' = x & y' = y & z' = z),
        mgr.Implies(mgr.And(pcs[9], x_pcs[5]),
                    mgr.And(mgr.Equals(x_w, w), mgr.Equals(x_x, x),
                            mgr.Equals(x_y, y), mgr.Equals(x_z, z))),
        # (pc = 9 & pc' = 10)  -> (w' = w & x' = x & y' = y & z' = z),
        mgr.Implies(mgr.And(pcs[9], x_pcs[10]),
                    mgr.And(mgr.Equals(x_w, w), mgr.Equals(x_x, x),
                            mgr.Equals(x_y, y), mgr.Equals(x_z, z))),
        # (pc = 10 & pc' = 11) -> (w' = w & x' = z*y + w/y & y' = y & z' = z),
        mgr.Implies(mgr.And(pcs[10], x_pcs[11]),
                    mgr.And(mgr.Equals(x_w, w),
                            mgr.Equals(x_x, mgr.Plus(mgr.Times(z, y),
                                                     mgr.Div(w, y))),
                            mgr.Equals(x_y, y), mgr.Equals(x_z, z))),
        # (pc = 11 & pc' = 12) -> (w' = w & x' = x & y' = y+1 & z' = z),
        mgr.Implies(mgr.And(pcs[11], x_pcs[12]),
                    mgr.And(mgr.Equals(x_w, w), mgr.Equals(x_x, x),
                            mgr.Equals(x_y, mgr.Plus(y, ints[1])),
                            mgr.Equals(x_z, z))),
        # (pc = 12 & pc' = 9)  -> (w' = w & x' = x & y' = y & z' = z+1),
        mgr.Implies(mgr.And(pcs[12], x_pcs[9]),
                    mgr.And(mgr.Equals(x_w, w), mgr.Equals(x_x, x),
                            mgr.Equals(x_y, y),
                            mgr.Equals(x_z, mgr.Plus(z, ints[1])))),
        # (pc = 13 & pc' = -1) -> (w' = w & x' = x & y' = y & z' = z),
        mgr.Implies(mgr.And(pcs[13], x_pcend),
                    mgr.And(mgr.Equals(x_w, w), mgr.Equals(x_x, x),
                            mgr.Equals(x_y, y), mgr.Equals(x_z, z))),
        # (pc = 13 & pc' = 14) -> (w' = w & x' = x & y' = y & z' = z),
        mgr.Implies(mgr.And(pcs[13], x_pcs[14]),
                    mgr.And(mgr.Equals(x_w, w), mgr.Equals(x_x, x),
                            mgr.Equals(x_y, y), mgr.Equals(x_z, z))),
        # (pc = 14 & pc' = -1) -> (w' = w & x' = x & y' = y & z' = z),
        mgr.Implies(mgr.And(pcs[14], x_pcend),
                    mgr.And(mgr.Equals(x_w, w), mgr.Equals(x_x, x),
                            mgr.Equals(x_y, y), mgr.Equals(x_z, z))),
        # (pc = 14 & pc' = 15) -> (w' = w & x' = x & y' = y & z' = z),
        mgr.Implies(mgr.And(pcs[14], x_pcs[15]),
                    mgr.And(mgr.Equals(x_w, w), mgr.Equals(x_x, x),
                            mgr.Equals(x_y, y), mgr.Equals(x_z, z))),
        # (pc = 15 & pc' = -1) -> (w' = w & x' = x & y' = y & z' = z),
        mgr.Implies(mgr.And(pcs[15], x_pcend),
                    mgr.And(mgr.Equals(x_w, w), mgr.Equals(x_x, x),
                            mgr.Equals(x_y, y), mgr.Equals(x_z, z)))
    )

    # transition relation.
    trans = mgr.And(cfg, labels)

    # fairness.
    fairness = mgr.Not(pcend)

    return symbols, init, trans, fairness
