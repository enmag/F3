import pysmt.typing as types
from pysmt.environment import Environment as PysmtEnv
from pysmt.fnode import FNode
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

    n_locs = 21
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
        # pc = 0 & !(z >= 4) : -1,
        mgr.Implies(mgr.And(pcs[0], mgr.Not(mgr.GE(z, ints[4]))), x_pcend),
        # pc = 0 & z >= 4 : 1,
        mgr.Implies(mgr.And(pcs[0], mgr.GE(z, ints[4])), x_pcs[1]),
        # pc = 1 : 2,
        mgr.Implies(pcs[1], x_pcs[2]),
        # pc = 2 & x >= 0 : 3,
        mgr.Implies(mgr.And(pcs[2], mgr.GE(x, ints[0])), x_pcs[3]),
        # pc = 2 & !(x >= 0) : 5,
        mgr.Implies(mgr.And(pcs[2], mgr.Not(mgr.GE(x, ints[0]))), x_pcs[5]),
        # pc = 3 & !(w <= -5) : -1,
        mgr.Implies(mgr.And(pcs[3], mgr.Not(mgr.LE(w, mgr.Int(-5)))), x_pcend),
        # pc = 3 & w <= -5 : 4,
        mgr.Implies(mgr.And(pcs[3], mgr.LE(w, mgr.Int(-5))), x_pcs[4]),
        # pc = 4 : 6,
        mgr.Implies(pcs[4], x_pcs[6]),
        # pc = 5 : 6,
        mgr.Implies(pcs[5], x_pcs[6]),
        # pc = 6 : {7, 9},
        mgr.Implies(pcs[6], mgr.Or(x_pcs[7], x_pcs[9])),
        # pc = 7 & !(x < 0) : -1,
        mgr.Implies(mgr.And(pcs[7], mgr.Not(mgr.LT(x, ints[0]))), x_pcend),
        # pc = 7 & x < 0 : 8,
        mgr.Implies(mgr.And(pcs[7], mgr.LT(x, ints[0])), x_pcs[8]),
        # pc = 8 : -1,
        mgr.Implies(pcs[8], x_pcend),
        # pc = 9 & !(x >= w) : 18,
        mgr.Implies(mgr.And(pcs[9], mgr.Not(mgr.GE(x, w))), x_pcs[18]),
        # pc = 9 & x >= w : 10,
        mgr.Implies(mgr.And(pcs[9], mgr.GE(x, w)), x_pcs[10]),
        # pc = 10 : {11, 13},
        mgr.Implies(pcs[10], mgr.Or(x_pcs[11], x_pcs[13])),
        # pc = 11 & !(x < 0) : -1,
        mgr.Implies(mgr.And(pcs[11], mgr.Not(mgr.LT(x, ints[0]))), x_pcend),
        # pc = 11 & x < 0 : 12,
        mgr.Implies(mgr.And(pcs[11], mgr.LT(x, ints[0])), x_pcs[12]),
        # pc = 12 : -1,
        mgr.Implies(pcs[12], x_pcend),
        # pc = 13 & z <= 8 : 14,
        mgr.Implies(mgr.And(pcs[13], mgr.LE(z, ints[8])), x_pcs[14]),
        # pc = 13 & !(z <= 8) : 15,
        mgr.Implies(mgr.And(pcs[13], mgr.Not(mgr.LE(z, ints[8]))), x_pcs[15]),
        # pc = 14 : 16,
        mgr.Implies(pcs[14], x_pcs[16]),
        # pc = 15 : 16,
        mgr.Implies(pcs[15], x_pcs[16]),
        # pc = 16 : 17,
        mgr.Implies(pcs[16], x_pcs[17]),
        # pc = 17 : 9,
        mgr.Implies(pcs[17], x_pcs[9]),
        # pc = 18 : {-1, 19},
        mgr.Implies(pcs[18], mgr.Or(x_pcend, x_pcs[19])),
        # pc = 19 & !(x < 0) : -1,
        mgr.Implies(mgr.And(pcs[19], mgr.Not(mgr.LT(x, ints[0]))), x_pcend),
        # pc = 19 & x < 0 : 20,
        mgr.Implies(mgr.And(pcs[19], mgr.LT(x, ints[0])), x_pcs[20]),
        # pc = 20 : -1,
        mgr.Implies(pcs[20], x_pcend)
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
        # (pc = 1 & pc' = 2)   -> (w' = w & x' = x & y' = y & z' = z+1),
        mgr.Implies(mgr.And(pcs[1], x_pcs[2]),
                    mgr.And(mgr.Equals(x_w, w), mgr.Equals(x_x, x),
                            mgr.Equals(x_y, y),
                            mgr.Equals(x_z, mgr.Plus(z, ints[1])))),
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
        # (pc = 4 & pc' = 6)   -> (w' = w & x' = x & y' = y & z' = z+1),
        mgr.Implies(mgr.And(pcs[4], x_pcs[6]),
                    mgr.And(mgr.Equals(x_w, w), mgr.Equals(x_x, x),
                            mgr.Equals(x_y, y),
                            mgr.Equals(x_z, mgr.Plus(z, ints[1])))),
        # (pc = 5 & pc' = 6)   -> (w' = w & x' = x & y' = y & z' = z-1),
        mgr.Implies(mgr.And(pcs[5], x_pcs[6]),
                    mgr.And(mgr.Equals(x_w, w), mgr.Equals(x_x, x),
                            mgr.Equals(x_y, y),
                            mgr.Equals(x_z, mgr.Minus(z, ints[1])))),
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
        # (pc = 8 & pc' = -1)  -> (w' = w & x' = x & y' = y & z' = z-1),
        mgr.Implies(mgr.And(pcs[8], x_pcend),
                    mgr.And(mgr.Equals(x_w, w), mgr.Equals(x_x, x),
                            mgr.Equals(x_y, y),
                            mgr.Equals(x_z, mgr.Minus(z, ints[1])))),
        # (pc = 9 & pc' = 18)  -> (w' = w & x' = x & y' = y & z' = z),
        mgr.Implies(mgr.And(pcs[9], x_pcs[18]),
                    mgr.And(mgr.Equals(x_w, w), mgr.Equals(x_x, x),
                            mgr.Equals(x_y, y), mgr.Equals(x_z, z))),
        # (pc = 9 & pc' = 10)  -> (w' = w & x' = x & y' = y & z' = z),
        mgr.Implies(mgr.And(pcs[9], x_pcs[10]),
                    mgr.And(mgr.Equals(x_w, w), mgr.Equals(x_x, x),
                            mgr.Equals(x_y, y), mgr.Equals(x_z, z))),
        # (pc = 10 & pc' = 11) -> (w' = w & x' = x & y' = y & z' = z),
        mgr.Implies(mgr.And(pcs[10], x_pcs[11]),
                    mgr.And(mgr.Equals(x_w, w), mgr.Equals(x_x, x),
                            mgr.Equals(x_y, y), mgr.Equals(x_z, z))),
        # (pc = 10 & pc' = 13) -> (w' = w & x' = x & y' = y & z' = z),
        mgr.Implies(mgr.And(pcs[10], x_pcs[13]),
                    mgr.And(mgr.Equals(x_w, w), mgr.Equals(x_x, x),
                            mgr.Equals(x_y, y), mgr.Equals(x_z, z))),
        # (pc = 11 & pc' = -1) -> (w' = w & x' = x & y' = y & z' = z),
        mgr.Implies(mgr.And(pcs[11], x_pcend),
                    mgr.And(mgr.Equals(x_w, w), mgr.Equals(x_x, x),
                            mgr.Equals(x_y, y), mgr.Equals(x_z, z))),
        # (pc = 11 & pc' = 12) -> (w' = w & x' = x & y' = y & z' = z),
        mgr.Implies(mgr.And(pcs[11], x_pcs[12]),
                    mgr.And(mgr.Equals(x_w, w), mgr.Equals(x_x, x),
                            mgr.Equals(x_y, y), mgr.Equals(x_z, z))),
        # (pc = 12 & pc' = -1) -> (w' = w & x' = x & y' = y & z' = z-1),
        mgr.Implies(mgr.And(pcs[12], x_pcend),
                    mgr.And(mgr.Equals(x_w, w), mgr.Equals(x_x, x),
                            mgr.Equals(x_y, y),
                            mgr.Equals(x_z, mgr.Minus(z, ints[1])))),
        # (pc = 13 & pc' = 14) -> (w' = w & x' = x & y' = y & z' = z),
        mgr.Implies(mgr.And(pcs[13], x_pcs[14]),
                    mgr.And(mgr.Equals(x_w, w), mgr.Equals(x_x, x),
                            mgr.Equals(x_y, y), mgr.Equals(x_z, z))),
        # (pc = 13 & pc' = 15) -> (w' = w & x' = x & y' = y & z' = z),
        mgr.Implies(mgr.And(pcs[13], x_pcs[15]),
                    mgr.And(mgr.Equals(x_w, w), mgr.Equals(x_x, x),
                            mgr.Equals(x_y, y), mgr.Equals(x_z, z))),
        # (pc = 14 & pc' = 16) -> (w' = w & x' = x & y' = y & z' = z),
        mgr.Implies(mgr.And(pcs[14], x_pcs[16]),
                    mgr.And(mgr.Equals(x_w, w), mgr.Equals(x_x, x),
                            mgr.Equals(x_y, y), mgr.Equals(x_z, z))),
        # (pc = 15 & pc' = 16) -> (w' = w & x' = x & y' = y & z' = z),
        mgr.Implies(mgr.And(pcs[15], x_pcs[16]),
                    mgr.And(mgr.Equals(x_w, w), mgr.Equals(x_x, x),
                            mgr.Equals(x_y, y), mgr.Equals(x_z, z))),
        # (pc = 16 & pc' = 17) -> (w' = w & x' = z*z & y' = y & z' = z),
        mgr.Implies(mgr.And(pcs[16], x_pcs[17]),
                    mgr.And(mgr.Equals(x_w, w),
                            mgr.Equals(x_x, mgr.Times(z, z)),
                            mgr.Equals(x_y, y), mgr.Equals(x_z, z))),
        # (pc = 17 & pc' = 9)  -> (w' = w-1 & x' = x & y' = y & z' = z),
        mgr.Implies(mgr.And(pcs[17], x_pcs[9]),
                    mgr.And(mgr.Equals(x_w, mgr.Minus(w, ints[1])),
                            mgr.Equals(x_x, x), mgr.Equals(x_y, y),
                            mgr.Equals(x_z, z))),
        # (pc = 18 & pc' = -1) -> (w' = w & x' = x & y' = y & z' = z),
        mgr.Implies(mgr.And(pcs[18], x_pcend),
                    mgr.And(mgr.Equals(x_w, w), mgr.Equals(x_x, x),
                            mgr.Equals(x_y, y), mgr.Equals(x_z, z))),
        # (pc = 18 & pc' = 19) -> (w' = w & x' = x & y' = y & z' = z),
        mgr.Implies(mgr.And(pcs[18], x_pcs[19]),
                    mgr.And(mgr.Equals(x_w, w), mgr.Equals(x_x, x),
                            mgr.Equals(x_y, y), mgr.Equals(x_z, z))),
        # (pc = 19 & pc' = -1) -> (w' = w & x' = x & y' = y & z' = z),
        mgr.Implies(mgr.And(pcs[19], x_pcend),
                    mgr.And(mgr.Equals(x_w, w), mgr.Equals(x_x, x),
                            mgr.Equals(x_y, y), mgr.Equals(x_z, z))),
        # (pc = 19 & pc' = 20) -> (w' = w & x' = x & y' = y & z' = z),
        mgr.Implies(mgr.And(pcs[19], x_pcs[20]),
                    mgr.And(mgr.Equals(x_w, w), mgr.Equals(x_x, x),
                            mgr.Equals(x_y, y), mgr.Equals(x_z, z))),
        # (pc = 20 & pc' = -1) -> (w' = w & x' = x & y' = y & z' = z-1),
        mgr.Implies(mgr.And(pcs[20], x_pcend),
                    mgr.And(mgr.Equals(x_w, w), mgr.Equals(x_x, x),
                            mgr.Equals(x_y, y),
                            mgr.Equals(x_z, mgr.Minus(z, ints[1]))))
    )

    # transition relation.
    trans = mgr.And(cfg, labels)

    # fairness.
    fairness = mgr.Not(pcend)

    return symbols, init, trans, fairness
