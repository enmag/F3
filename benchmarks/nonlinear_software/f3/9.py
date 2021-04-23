import pysmt.typing as types
from pysmt.environment import Environment as PysmtEnv
from pysmt.fnode import FNode
from utils import symb_to_next


def transition_system(env: PysmtEnv) -> (frozenset, FNode, FNode, FNode):
    assert isinstance(env, PysmtEnv)
    mgr = env.formula_manager
    pc = mgr.Symbol("pc", types.INT)
    x = mgr.Symbol("x", types.INT)
    y = mgr.Symbol("y", types.INT)
    x_pc = symb_to_next(mgr, pc)
    x_x = symb_to_next(mgr, x)
    x_y = symb_to_next(mgr, y)
    symbols = frozenset([pc, x, y])

    n_locs = 8
    int_bound = 33
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
        # pc = 0 & !(x >= 1) : -1,
        mgr.Implies(mgr.And(pcs[0], mgr.Not(mgr.GE(x, ints[1]))), x_pcend),
        # pc = 0 & x >= 1 : 1,
        mgr.Implies(mgr.And(pcs[0], mgr.GE(x, ints[1])), x_pcs[1]),
        # pc = 1 & !(x >= 0) : -1,
        mgr.Implies(mgr.And(pcs[1], mgr.Not(mgr.GE(x, ints[0]))), x_pcend),
        # pc = 1 & x >= 0 : 2,
        mgr.Implies(mgr.And(pcs[1], mgr.GE(x, ints[0])), x_pcs[2]),
        # pc = 2 & !(y >= 32) : -1,
        mgr.Implies(mgr.And(pcs[2], mgr.Not(mgr.GE(y, ints[32]))), x_pcend),
        # pc = 2 & y >= 32 : 3,
        mgr.Implies(mgr.And(pcs[2], mgr.GE(y, ints[32])), x_pcs[3]),
        # pc = 3 : {4, 6},
        mgr.Implies(pcs[3], mgr.Or(x_pcs[4], x_pcs[6])),
        # pc = 4 : 5,
        mgr.Implies(pcs[4], x_pcs[5]),
        # pc = 5 : 1,
        mgr.Implies(pcs[5], x_pcs[1]),
        # pc = 6 : 7,
        mgr.Implies(pcs[6], x_pcs[7]),
        # pc = 7 : 1,
        mgr.Implies(pcs[7], x_pcs[1]))

    # transition labels.
    labels = mgr.And(
        # (pc = -1 & pc' = -1) -> (x' = x & y' = y),
        mgr.Implies(mgr.And(pcend, x_pcend),
                    mgr.And(mgr.Equals(x_x, x), mgr.Equals(x_y, y))),
        # (pc = 0 & pc' = -1) -> (x' = x & y' = y),
        mgr.Implies(mgr.And(pcs[0], x_pcend),
                    mgr.And(mgr.Equals(x_x, x), mgr.Equals(x_y, y))),
        # (pc = 0 & pc' = 1) -> (x' = x & y' = y),
        mgr.Implies(mgr.And(pcs[0], x_pcs[1]),
                    mgr.And(mgr.Equals(x_x, x), mgr.Equals(x_y, y))),
        # (pc = 1 & pc' = -1) -> (x' = x & y' = y),
        mgr.Implies(mgr.And(pcs[1], x_pcend),
                    mgr.And(mgr.Equals(x_x, x), mgr.Equals(x_y, y))),
        # (pc = 1 & pc' = 2) -> (x' = x & y' = y),
        mgr.Implies(mgr.And(pcs[1], x_pcs[2]),
                    mgr.And(mgr.Equals(x_x, x), mgr.Equals(x_y, y))),
        # (pc = 2 & pc' = -1) -> (x' = x & y' = y),
        mgr.Implies(mgr.And(pcs[2], x_pcend),
                    mgr.And(mgr.Equals(x_x, x), mgr.Equals(x_y, y))),
        # (pc = 2 & pc' = 3) -> (x' = x & y' = y),
        mgr.Implies(mgr.And(pcs[2], x_pcs[3]),
                    mgr.And(mgr.Equals(x_x, x), mgr.Equals(x_y, y))),
        # (pc = 3 & pc' = 4) -> (x' = x & y' = y),
        mgr.Implies(mgr.And(pcs[3], x_pcs[4]),
                    mgr.And(mgr.Equals(x_x, x), mgr.Equals(x_y, y))),
        # (pc = 3 & pc' = 6) -> (x' = x & y' = y),
        mgr.Implies(mgr.And(pcs[3], x_pcs[6]),
                    mgr.And(mgr.Equals(x_x, x), mgr.Equals(x_y, y))),
        # (pc = 4 & pc' = 5) -> (x' = 1 & y' = y),
        mgr.Implies(mgr.And(pcs[4], x_pcs[5]),
                    mgr.And(mgr.Equals(x_x, ints[1]), mgr.Equals(x_y, y))),
        # (pc = 5 & pc' = 1) -> (x' = x & y' = 15),
        mgr.Implies(mgr.And(pcs[5], x_pcs[1]),
                    mgr.And(mgr.Equals(x_x, x), mgr.Equals(x_y, ints[15]))),
        # (pc = 6 & pc' = 7) -> (              y' = x),
        mgr.Implies(mgr.And(pcs[6], x_pcs[7]), mgr.And(mgr.Equals(x_y, x))),
        # (pc = 7 & pc' = 1) -> (x' = x & y' = y),
        mgr.Implies(mgr.And(pcs[7], x_pcs[1]),
                    mgr.And(mgr.Equals(x_x, x), mgr.Equals(x_y, y))))

    # transition relation.
    trans = mgr.And(cfg, labels)

    # fairness.
    fairness = mgr.Not(pcend)

    return symbols, init, trans, fairness
