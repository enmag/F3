import pysmt.typing as types
from pysmt.environment import Environment as PysmtEnv
from pysmt.fnode import FNode
from utils import symb_to_next


def transition_system(env: PysmtEnv) -> (frozenset, FNode, FNode, FNode):
    assert isinstance(env, PysmtEnv)
    mgr = env.formula_manager
    i = mgr.Symbol("i", types.INT)
    j = mgr.Symbol("j", types.INT)
    k = mgr.Symbol("k", types.INT)
    m = mgr.Symbol("m", types.INT)
    pc = mgr.Symbol("pc", types.INT)
    x_i = symb_to_next(mgr, i)
    x_j = symb_to_next(mgr, j)
    x_k = symb_to_next(mgr, k)
    x_m = symb_to_next(mgr, m)
    x_pc = symb_to_next(mgr, pc)
    symbols = frozenset([i, j, k, m, pc])

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
        # pc = 0 & !(j >= 2) : -1,
        mgr.Implies(mgr.And(pcs[0], mgr.Not(mgr.GE(j, ints[2]))), x_pcend),
        # pc = 0 & j >= 2 : 1,
        mgr.Implies(mgr.And(pcs[0], mgr.GE(j, ints[2])), x_pcs[1]),
        # pc = 1 & !(k >= 3) : -1,
        mgr.Implies(mgr.And(pcs[1], mgr.Not(mgr.GE(k, ints[3]))), x_pcend),
        # pc = 1 & k >= 3 : 2,
        mgr.Implies(mgr.And(pcs[1], mgr.GE(k, ints[3])), x_pcs[2]),
        # pc = 2 & !(i >= 0 & m >= 0) : -1,
        mgr.Implies(
            mgr.And(pcs[2],
                    mgr.Not(mgr.And(mgr.GE(i, ints[0]), mgr.GE(m, ints[0])))),
            x_pcend),
        # pc = 2 & i >= 0 & m >= 0 : 3,
        mgr.Implies(
            mgr.And(pcs[2], mgr.And(mgr.GE(i, ints[0]), mgr.GE(m, ints[0]))),
            x_pcs[3]),
        # pc = 3 : 4,
        mgr.Implies(pcs[3], x_pcs[4]),
        # pc = 4 : 2,
        mgr.Implies(pcs[4], x_pcs[2]))

    # transition labels.
    labels = mgr.And(
        # (pc = -1 & pc' = -1) -> (i' = i & j' = j & k' = k & m' = m),
        mgr.Implies(
            mgr.And(pcend, x_pcend),
            mgr.And(mgr.Equals(x_i, i), mgr.Equals(x_j, j), mgr.Equals(x_k, k),
                    mgr.Equals(x_m, m))),
        # (pc = 0 & pc' = -1) -> (i' = i & j' = j & k' = k & m' = m),
        mgr.Implies(
            mgr.And(pcs[0], x_pcend),
            mgr.And(mgr.Equals(x_i, i), mgr.Equals(x_j, j), mgr.Equals(x_k, k),
                    mgr.Equals(x_m, m))),
        # (pc = 0 & pc' = 1)  -> (i' = i & j' = j & k' = k & m' = m),
        mgr.Implies(
            mgr.And(pcs[0], x_pcs[1]),
            mgr.And(mgr.Equals(x_i, i), mgr.Equals(x_j, j), mgr.Equals(x_k, k),
                    mgr.Equals(x_m, m))),
        # (pc = 1 & pc' = -1) -> (i' = i & j' = j & k' = k & m' = m),
        mgr.Implies(
            mgr.And(pcs[1], x_pcend),
            mgr.And(mgr.Equals(x_i, i), mgr.Equals(x_j, j), mgr.Equals(x_k, k),
                    mgr.Equals(x_m, m))),
        # (pc = 1 & pc' = 2)  -> (i' = i & j' = j & k' = k & m' = m),
        mgr.Implies(
            mgr.And(pcs[1], x_pcs[2]),
            mgr.And(mgr.Equals(x_i, i), mgr.Equals(x_j, j), mgr.Equals(x_k, k),
                    mgr.Equals(x_m, m))),
        # (pc = 2 & pc' = -1) -> (i' = i & j' = j & k' = k & m' = m),
        mgr.Implies(
            mgr.And(pcs[2], x_pcend),
            mgr.And(mgr.Equals(x_i, i), mgr.Equals(x_j, j), mgr.Equals(x_k, k),
                    mgr.Equals(x_m, m))),
        # (pc = 2 & pc' = 3)  -> (i' = i & j' = j & k' = k & m' = m),
        mgr.Implies(
            mgr.And(pcs[2], x_pcs[3]),
            mgr.And(mgr.Equals(x_i, i), mgr.Equals(x_j, j), mgr.Equals(x_k, k),
                    mgr.Equals(x_m, m))),
        # (pc = 3 & pc' = 4)  -> (i' = j*k & j' = j & k' = k & m' = m),
        mgr.Implies(
            mgr.And(pcs[3], x_pcs[4]),
            mgr.And(mgr.Equals(x_i, mgr.Times(j, k)), mgr.Equals(x_j, j),
                    mgr.Equals(x_k, k), mgr.Equals(x_m, m))),
        # (pc = 4 & pc' = 2)  -> (i' = i & j' = j & k' = k          ),
        mgr.Implies(
            mgr.And(pcs[4], x_pcs[2]),
            mgr.And(mgr.Equals(x_i, i), mgr.Equals(x_j, j),
                    mgr.Equals(x_k, k))))

    # transition relation.
    trans = mgr.And(cfg, labels)

    # fairness.
    fairness = mgr.Not(pcend)

    return symbols, init, trans, fairness
