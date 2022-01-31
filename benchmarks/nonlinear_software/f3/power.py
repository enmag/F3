import pysmt.typing as types
from typing import Tuple, FrozenSet
from pysmt.environment import Environment as PysmtEnv
from pysmt.fnode import FNode
from expr_utils import symb2next


def transition_system(env: PysmtEnv) -> Tuple[FrozenSet[FNode], FNode, FNode, FNode]:
    assert isinstance(env, PysmtEnv)
    mgr = env.formula_manager
    e = mgr.Symbol("e", types.INT)
    i = mgr.Symbol("i", types.INT)
    n = mgr.Symbol("n", types.INT)
    pc = mgr.Symbol("pc", types.INT)
    x_e = symb2next(env, e)
    x_i = symb2next(env, i)
    x_n = symb2next(env, n)
    x_pc = symb2next(env, pc)
    symbols = frozenset([e, i, n, pc])

    n_locs = 6
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
        # pc = 0 & !(n >= 2) : -1,
        mgr.Implies(mgr.And(pcs[0], mgr.Not(mgr.GE(n, ints[2]))), x_pcend),
        # pc = 0 & n >= 2 : 1,
        mgr.Implies(mgr.And(pcs[0], mgr.GE(n, ints[2])), x_pcs[1]),
        # pc = 1 : 2,
        mgr.Implies(pcs[1], x_pcs[2]),
        # pc = 2 : 3,
        mgr.Implies(pcs[2], x_pcs[3]),
        # pc = 3 & !(i <= e) : -1,
        mgr.Implies(mgr.And(pcs[3], mgr.Not(mgr.LE(i, e))), x_pcend),
        # pc = 3 & i <= e : 4,
        mgr.Implies(mgr.And(pcs[3], mgr.LE(i, e)), x_pcs[4]),
        # pc = 4 : 5,
        mgr.Implies(pcs[4], x_pcs[5]),
        # pc = 5 : 3,
        mgr.Implies(pcs[5], x_pcs[3]))

    # transition labels.
    labels = mgr.And(
        # (pc = -1 & pc' = -1) -> (n' = n & i' = i & e' = e),
        mgr.Implies(
            mgr.And(pcend, x_pcend),
            mgr.And(mgr.Equals(x_n, n), mgr.Equals(x_i, i),
                    mgr.Equals(x_e, e))),
        # (pc = 0 & pc' = -1) -> (n' = n & i' = i & e' = e),
        mgr.Implies(
            mgr.And(pcs[0], x_pcend),
            mgr.And(mgr.Equals(x_n, n), mgr.Equals(x_i, i),
                    mgr.Equals(x_e, e))),
        # (pc = 0 & pc' = 1)  -> (n' = n & i' = i & e' = e),
        mgr.Implies(
            mgr.And(pcs[0], x_pcs[1]),
            mgr.And(mgr.Equals(x_n, n), mgr.Equals(x_i, i),
                    mgr.Equals(x_e, e))),
        # (pc = 1 & pc' = 2)  -> (n' = n & i' = 1 & e' = e),
        mgr.Implies(
            mgr.And(pcs[1], x_pcs[2]),
            mgr.And(mgr.Equals(x_n, n), mgr.Equals(x_i, ints[1]),
                    mgr.Equals(x_e, e))),
        # (pc = 2 & pc' = 3)  -> (n' = n & i' = i & e' = 1),
        mgr.Implies(
            mgr.And(pcs[2], x_pcs[3]),
            mgr.And(mgr.Equals(x_n, n), mgr.Equals(x_i, i),
                    mgr.Equals(x_e, ints[1]))),
        # (pc = 3 & pc' = -1) -> (n' = n & i' = i & e' = e),
        mgr.Implies(
            mgr.And(pcs[3], x_pcend),
            mgr.And(mgr.Equals(x_n, n), mgr.Equals(x_i, i),
                    mgr.Equals(x_e, e))),
        # (pc = 3 & pc' = 4)  -> (n' = n & i' = i & e' = e),
        mgr.Implies(
            mgr.And(pcs[3], x_pcs[4]),
            mgr.And(mgr.Equals(x_n, n), mgr.Equals(x_i, i),
                    mgr.Equals(x_e, e))),
        # (pc = 4 & pc' = 5)  -> (n' = n & i' = i & e' = e*n),
        mgr.Implies(
            mgr.And(pcs[4], x_pcs[5]),
            mgr.And(mgr.Equals(x_n, n), mgr.Equals(x_i, i),
                    mgr.Equals(x_e, mgr.Times(e, n)))),
        # (pc = 5 & pc' = 3)  -> (n' = n & i' = i+1 & e' = e),
        mgr.Implies(
            mgr.And(pcs[5], x_pcs[3]),
            mgr.And(mgr.Equals(x_n, n), mgr.Equals(x_i, mgr.Plus(i, ints[1])),
                    mgr.Equals(x_e, e))))

    # transition relation.
    trans = mgr.And(cfg, labels)

    # fairness.
    fairness = mgr.Not(pcend)

    return symbols, init, trans, fairness
