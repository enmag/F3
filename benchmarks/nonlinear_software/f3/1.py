from pysmt.environment import Environment as PysmtEnv
from pysmt.fnode import FNode
import pysmt.typing as types

from utils import symb_to_next


def transition_system(env: PysmtEnv) -> (frozenset, FNode, FNode, FNode):
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

    m_1 = mgr.Int(-1)
    ints = [mgr.Int(i) for i in range(0, 9)]

    # initial location.
    init = mgr.Equals(pc, ints[0])

    # control flow graph.
    cfg = mgr.And(
        # pc = -1 : -1,
        mgr.Implies(mgr.Equals(pc, m_1), mgr.Equals(x_pc, m_1)),
        # pc = 0 : 1,
        mgr.Implies(mgr.Equals(pc, ints[0]), mgr.Equals(x_pc, ints[1])),
        # pc = 1 & !(x >= y) : -1,
        mgr.Implies(mgr.And(mgr.Equals(pc, ints[1]),
                            mgr.Not(mgr.GE(x, y))), mgr.Equals(x_pc, m_1)),
        # pc = 1 & (x >= y) : 2,
        mgr.Implies(mgr.And(mgr.Equals(pc, m_1), mgr.GE(x, y)),
                    mgr.Equals(x_pc, ints[2])),
        # pc = 2 : 3,
        mgr.Implies(mgr.Equals(pc, ints[2]), mgr.Equals(x_pc, ints[3])),
        # pc = 3 : 4,
        mgr.Implies(mgr.Equals(pc, ints[3]), mgr.Equals(x_pc, ints[4])),
        # pc = 4 & !(z >= 0) : -1,
        mgr.Implies(mgr.And(mgr.Equals(pc, ints[4]),
                            mgr.Not(mgr.GE(z, ints[0]))),
                    mgr.Equals(x_pc, m_1)),
        # pc = 4 & z >= 0 : 5,
        mgr.Implies(mgr.And(mgr.Equals(pc, ints[4]), mgr.GE(z, ints[0])),
                    mgr.Equals(x_pc, ints[5])),
        # pc = 5 & !(x <= y - 1) : -1,
        mgr.Implies(mgr.And(mgr.Equals(pc, ints[5]),
                            mgr.Not(mgr.LE(x, mgr.Minus(y, ints[1])))),
                    mgr.Equals(x_pc, m_1)),
        # pc = 5 & x <= y - 1 : 6,
        mgr.Implies(mgr.And(mgr.Equals(pc, ints[5]),
                            mgr.LE(x, mgr.Minus(y, ints[1]))),
                    mgr.Equals(x_pc, ints[6])),
        # pc = 6 : 7,
        mgr.Implies(mgr.Equals(pc, ints[6]), mgr.Equals(x_pc, ints[7])),
        # pc = 7 : 8,
        mgr.Implies(mgr.Equals(pc, ints[7]), mgr.Equals(x_pc, ints[8])),
        # pc = 8 : 5,
        mgr.Implies(mgr.Equals(pc, ints[8]), mgr.Equals(x_pc, ints[5]))
    )

    # transition labels.
    labels = mgr.And(
        # (pc = -1 & pc' = -1) -> (x' = x & y' = y & z' = z),
        mgr.Implies(mgr.And(mgr.Equals(pc, m_1), mgr.Equals(x_pc, m_1)),
                    mgr.And(mgr.Equals(x_x, x), mgr.Equals(x_y, y),
                            mgr.Equals(x_z, z))),
        # (pc = 0 & pc' = 1)  -> (x' = x & y' = y & z' = 2),
        mgr.Implies(mgr.And(mgr.Equals(pc, ints[0]),
                            mgr.Equals(x_pc, ints[1])),
                    mgr.And(mgr.Equals(x_x, x), mgr.Equals(x_y, y),
                            mgr.Equals(x_z, ints[2]))),
        # (pc = 1 & pc' = -1) -> (x' = x & y' = y & z' = z),
        mgr.Implies(mgr.And(mgr.Equals(pc, ints[1]), mgr.Equals(x_pc, m_1)),
                    mgr.And(mgr.Equals(x_x, x), mgr.Equals(x_y, y),
                            mgr.Equals(x_z, z))),
        # (pc = 1 & pc' = 2)  -> (x' = x & y' = y & z' = z),
        mgr.Implies(mgr.And(mgr.Equals(pc, ints[1]),
                            mgr.Equals(x_pc, ints[2])),
                    mgr.And(mgr.Equals(x_x, x), mgr.Equals(x_y, y),
                            mgr.Equals(x_z, z))),
        # (pc = 2 & pc' = 3)  -> (x' = 5 & y' = y & z' = z),
        mgr.Implies(mgr.And(mgr.Equals(pc, ints[2]),
                            mgr.Equals(x_pc, ints[3])),
                    mgr.And(mgr.Equals(x_x, ints[5]), mgr.Equals(x_y, y),
                            mgr.Equals(x_z, z))),
        # (pc = 3 & pc' = 4)  -> (x' = x & y' = 6 & z' = z),
        mgr.Implies(mgr.And(mgr.Equals(pc, ints[3]),
                            mgr.Equals(x_pc, ints[4])),
                    mgr.And(mgr.Equals(x_x, x), mgr.Equals(x_y, ints[6]),
                            mgr.Equals(x_z, z))),
        # (pc = 4 & pc' = -1) -> (x' = x & y' = y & z' = z),
        mgr.Implies(mgr.And(mgr.Equals(pc, ints[4]), mgr.Equals(x_pc, m_1)),
                    mgr.And(mgr.Equals(x_x, x), mgr.Equals(x_y, y),
                            mgr.Equals(x_z, z))),
        # (pc = 4 & pc' = 5)  -> (x' = x & y' = y & z' = z),
        mgr.Implies(mgr.And(mgr.Equals(pc, ints[4]),
                            mgr.Equals(x_pc, ints[5])),
                    mgr.And(mgr.Equals(x_x, x), mgr.Equals(x_y, y),
                            mgr.Equals(x_z, z))),
        # (pc = 5 & pc' = -1) -> (x' = x & y' = y & z' = z),
        mgr.Implies(mgr.And(mgr.Equals(pc, ints[5]), mgr.Equals(x_pc, m_1)),
                    mgr.And(mgr.Equals(x_x, x), mgr.Equals(x_y, y),
                            mgr.Equals(x_z, z))),
        # (pc = 5 & pc' = 6)  -> (x' = x & y' = y & z' = z),
        mgr.Implies(mgr.And(mgr.Equals(pc, ints[5]),
                            mgr.Equals(x_pc, ints[6])),
                    mgr.And(mgr.Equals(x_x, x), mgr.Equals(x_y, y),
                            mgr.Equals(x_z, z))),
        # (pc = 6 & pc' = 7)  -> (x' = x & y' = z*z & z' = z),
        mgr.Implies(mgr.And(mgr.Equals(pc, ints[6]),
                            mgr.Equals(x_pc, ints[7])),
                    mgr.And(mgr.Equals(x_x, x),
                            mgr.Equals(x_y, mgr.Times(z, z)),
                            mgr.Equals(x_z, z))),
        # (pc = 7 & pc' = 8)  -> (x' = y & y' = y & z' = z),
        mgr.Implies(mgr.And(mgr.Equals(pc, ints[7]),
                            mgr.Equals(x_pc, ints[8])),
                    mgr.And(mgr.Equals(x_x, y), mgr.Equals(x_y, y),
                            mgr.Equals(x_z, z))),
        # (pc = 8 & pc' = 5)  -> (x' = x & y' = y+1 & z' = z),
        mgr.Implies(mgr.And(mgr.Equals(pc, ints[8]),
                            mgr.Equals(x_pc, ints[5])),
                    mgr.And(mgr.Equals(x_x, x),
                            mgr.Equals(x_y, mgr.Plus(y, ints[1])),
                            mgr.Equals(x_z, z)))
    )

    # transition relation.
    trans = mgr.And(cfg, labels)

    # fairness.
    fairness = mgr.Not(mgr.Equals(pc, m_1))

    return symbols, init, trans, fairness
