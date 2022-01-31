import pysmt.typing as types
from typing import Tuple, FrozenSet
from pysmt.environment import Environment as PysmtEnv
from pysmt.fnode import FNode
from expr_utils import symb2next


def transition_system(env: PysmtEnv) -> Tuple[FrozenSet[FNode], FNode, FNode, FNode]:
    assert isinstance(env, PysmtEnv)
    mgr = env.formula_manager
    pc = mgr.Symbol("pc", types.INT)
    x = mgr.Symbol("x", types.INT)
    y = mgr.Symbol("y", types.INT)
    z = mgr.Symbol("z", types.INT)
    x_pc = symb2next(env, pc)
    x_x = symb2next(env, x)
    x_y = symb2next(env, y)
    x_z = symb2next(env, z)
    symbols = frozenset([pc, x, y, z])

    n_locs = 7
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
        # pc = 0 & !(z >= 2) : -1,
        mgr.Implies(mgr.And(pcs[0], mgr.Not(mgr.GE(z, ints[2]))), x_pcend),
        # pc = 0 & z >= 2 : 1,
        mgr.Implies(mgr.And(pcs[0], mgr.GE(z, ints[2])), x_pcs[1]),
        # pc = 1 & !(y >= 3) : -1,
        mgr.Implies(mgr.And(pcs[1], mgr.Not(mgr.GE(y, ints[3]))), x_pcend),
        # pc = 1 & y >= 3 : 2,
        mgr.Implies(mgr.And(pcs[1], mgr.GE(y, ints[3])), x_pcs[2]),
        # pc = 2 & !(z >= -5) : -1,
        mgr.Implies(mgr.And(pcs[2], mgr.Not(mgr.GE(z, m_5))), x_pcend),
        # pc = 2 & z >= -5 : 3,
        mgr.Implies(mgr.And(pcs[2], mgr.GE(z, m_5)), x_pcs[3]),
        # pc = 3 & !(x >= 0) : 2,
        mgr.Implies(mgr.And(pcs[3], mgr.Not(mgr.GE(x, ints[0]))), x_pcs[2]),
        # pc = 3 & x >= 0 : 4,
        mgr.Implies(mgr.And(pcs[3], mgr.GE(x, ints[0])), x_pcs[4]),
        # pc = 4 : 5,
        mgr.Implies(pcs[4], x_pcs[5]),
        # pc = 5 : 6,
        mgr.Implies(pcs[5], x_pcs[6]),
        # pc = 6 : 3,
        mgr.Implies(pcs[6], x_pcs[3]))

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
        # (pc = 3 & pc' = 2)  -> (x' = x & y' = y & z' = z),
        mgr.Implies(
            mgr.And(pcs[3], x_pcs[2]),
            mgr.And(mgr.Equals(x_x, x), mgr.Equals(x_y, y),
                    mgr.Equals(x_z, z))),
        # (pc = 3 & pc' = 4)  -> (x' = x & y' = y & z' = z),
        mgr.Implies(
            mgr.And(pcs[3], x_pcs[4]),
            mgr.And(mgr.Equals(x_x, x), mgr.Equals(x_y, y),
                    mgr.Equals(x_z, z))),
        # (pc = 4 & pc' = 5)  -> (x' = z/y & y' = y & z' = z),
        mgr.Implies(
            mgr.And(pcs[4], x_pcs[5]),
            mgr.And(mgr.Equals(x_x, mgr.Div(z, y)), mgr.Equals(x_y, y),
                    mgr.Equals(x_z, z))),
        # (pc = 5 & pc' = 6)  -> (x' = x & y' = y+1 & z' = z),
        mgr.Implies(
            mgr.And(pcs[5], x_pcs[6]),
            mgr.And(mgr.Equals(x_x, x), mgr.Equals(x_y, mgr.Plus(y, ints[1])),
                    mgr.Equals(x_z, z))),
        # (pc = 6 & pc' = 3)  -> (x' = x & y' = y & z' = z+1),
        mgr.Implies(
            mgr.And(pcs[6], x_pcs[3]),
            mgr.And(mgr.Equals(x_x, x), mgr.Equals(x_y, y),
                    mgr.Equals(x_z, mgr.Plus(z, ints[1])))))

    # transition relation.
    trans = mgr.And(cfg, labels)

    # fairness.
    fairness = mgr.Not(pcend)

    return symbols, init, trans, fairness
