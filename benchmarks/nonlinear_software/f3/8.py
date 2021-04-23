import pysmt.typing as types
from pysmt.environment import Environment as PysmtEnv
from pysmt.fnode import FNode
from utils import symb_to_next


def transition_system(env: PysmtEnv) -> (frozenset, FNode, FNode, FNode):
    assert isinstance(env, PysmtEnv)
    mgr = env.formula_manager
    pc = mgr.Symbol("pc", types.INT)
    z = mgr.Symbol("z", types.INT)
    x_pc = symb_to_next(mgr, pc)
    x_z = symb_to_next(mgr, z)
    symbols = frozenset([pc, z])

    n_locs = 3
    int_bound = 4
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
        # pc = 0 & !(z >= 3) : -1,
        mgr.Implies(mgr.And(pcs[0], mgr.Not(mgr.GE(z, ints[3]))), x_pcend),
        # pc = 0 & z >= 3 : 1,
        mgr.Implies(mgr.And(pcs[0], mgr.GE(z, ints[3])), x_pcs[1]),
        # pc = 1 & !(z >= 3) : -1,
        mgr.Implies(mgr.And(pcs[1], mgr.Not(mgr.GE(z, ints[3]))), x_pcend),
        # pc = 1 & z >= 3 : 2,
        mgr.Implies(mgr.And(pcs[1], mgr.GE(z, ints[3])), x_pcs[2]),
        # pc = 2 : 1,
        mgr.Implies(pcs[2], x_pcs[1]))

    # transition labels.
    labels = mgr.And(
        # (pc = -1 & pc' = -1) -> (z' = z),
        mgr.Implies(mgr.And(pcend, x_pcend), mgr.And(mgr.Equals(x_z, z))),
        # (pc = 0 & pc' = -1) -> (z' = z),
        mgr.Implies(mgr.And(pcs[0], x_pcend), mgr.And(mgr.Equals(x_z, z))),
        # (pc = 0 & pc' = 1) -> (z' = z),
        mgr.Implies(mgr.And(pcs[0], x_pcs[1]), mgr.And(mgr.Equals(x_z, z))),
        # (pc = 1 & pc' = -1) -> (z' = z),
        mgr.Implies(mgr.And(pcs[1], x_pcend), mgr.And(mgr.Equals(x_z, z))),
        # (pc = 1 & pc' = 2) -> (z' = z),
        mgr.Implies(mgr.And(pcs[1], x_pcs[2]), mgr.And(mgr.Equals(x_z, z))))

    # transition relation.
    trans = mgr.And(cfg, labels)

    # fairness.
    fairness = mgr.Not(pcend)

    return symbols, init, trans, fairness
