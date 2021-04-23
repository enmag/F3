import pysmt.typing as types
from pysmt.environment import Environment as PysmtEnv
from pysmt.fnode import FNode
from utils import symb_to_next


def transition_system(env: PysmtEnv) -> (frozenset, FNode, FNode, FNode):
    assert isinstance(env, PysmtEnv)
    mgr = env.formula_manager
    d = mgr.Symbol("d", types.INT)
    log = mgr.Symbol("log", types.INT)
    n = mgr.Symbol("n", types.INT)
    pc = mgr.Symbol("pc", types.INT)
    x_d = symb_to_next(mgr, d)
    x_log = symb_to_next(mgr, log)
    x_n = symb_to_next(mgr, n)
    x_pc = symb_to_next(mgr, pc)
    symbols = frozenset([d, log, n, pc])

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
        # pc = 0 & !(n >= 1) : -1,
        mgr.Implies(mgr.And(pcs[0], mgr.Not(mgr.GE(n, ints[1]))), x_pcend),
        # pc = 0 & n >= 1 : 1,
        mgr.Implies(mgr.And(pcs[0], mgr.GE(n, ints[1])), x_pcs[1]),
        # pc = 1 & !(d >= 2) : -1,
        mgr.Implies(mgr.And(pcs[1], mgr.Not(mgr.GE(d, ints[2]))), x_pcend),
        # pc = 1 & d >= 2 : 2,
        mgr.Implies(mgr.And(pcs[1], mgr.GE(d, ints[2])), x_pcs[2]),
        # pc = 2 : 3,
        mgr.Implies(pcs[2], x_pcs[3]),
        # pc = 3 & !(n >= 0) : -1,
        mgr.Implies(mgr.And(pcs[3], mgr.Not(mgr.GE(n, ints[0]))), x_pcend),
        # pc = 3 & n >= 0 : 4,
        mgr.Implies(mgr.And(pcs[3], mgr.GE(n, ints[0])), x_pcs[4]),
        # pc = 4 : 5,
        mgr.Implies(pcs[4], x_pcs[5]),
        # pc = 5 : 3,
        mgr.Implies(pcs[5], x_pcs[3]))

    # transition labels.
    labels = mgr.And(
        # (pc = -1 & pc' = -1) -> (n' = n & d' = d & log' = log),
        mgr.Implies(
            mgr.And(pcend, x_pcend),
            mgr.And(mgr.Equals(x_n, n), mgr.Equals(x_d, d),
                    mgr.Equals(x_log, log))),
        # (pc = 0 & pc' = -1) -> (n' = n & d' = d & log' = log),
        mgr.Implies(
            mgr.And(pcs[0], x_pcend),
            mgr.And(mgr.Equals(x_n, n), mgr.Equals(x_d, d),
                    mgr.Equals(x_log, log))),
        # (pc = 0 & pc' = 1)  -> (n' = n & d' = d & log' = log),
        mgr.Implies(
            mgr.And(pcs[0], x_pcs[1]),
            mgr.And(mgr.Equals(x_n, n), mgr.Equals(x_d, d),
                    mgr.Equals(x_log, log))),
        # (pc = 1 & pc' = -1) -> (n' = n & d' = d & log' = log),
        mgr.Implies(
            mgr.And(pcs[1], x_pcend),
            mgr.And(mgr.Equals(x_n, n), mgr.Equals(x_d, d),
                    mgr.Equals(x_log, log))),
        # (pc = 1 & pc' = 2)  -> (n' = n & d' = d & log' = log),
        mgr.Implies(
            mgr.And(pcs[1], x_pcs[2]),
            mgr.And(mgr.Equals(x_n, n), mgr.Equals(x_d, d),
                    mgr.Equals(x_log, log))),
        # (pc = 2 & pc' = 3)  -> (n' = n & d' = d & log' = 0),
        mgr.Implies(
            mgr.And(pcs[2], x_pcs[3]),
            mgr.And(mgr.Equals(x_n, n), mgr.Equals(x_d, d),
                    mgr.Equals(x_log, ints[0]))),
        # (pc = 3 & pc' = -1) -> (n' = n & d' = d & log' = log),
        mgr.Implies(
            mgr.And(pcs[3], x_pcend),
            mgr.And(mgr.Equals(x_n, n), mgr.Equals(x_d, d),
                    mgr.Equals(x_log, log))),
        # (pc = 3 & pc' = 4)  -> (n' = n & d' = d & log' = log),
        mgr.Implies(
            mgr.And(pcs[3], x_pcs[4]),
            mgr.And(mgr.Equals(x_n, n), mgr.Equals(x_d, d),
                    mgr.Equals(x_log, log))),
        # (pc = 4 & pc' = 5)  -> (n' = n/d & d' = d & log' = log),
        mgr.Implies(
            mgr.And(pcs[4], x_pcs[5]),
            mgr.And(mgr.Equals(x_n, mgr.Div(n, d)), mgr.Equals(x_d, d),
                    mgr.Equals(x_log, log))),
        # (pc = 5 & pc' = 3)  -> (n' = n & d' = d & log' = log+1),
        mgr.Implies(
            mgr.And(pcs[5], x_pcs[3]),
            mgr.And(mgr.Equals(x_n, n), mgr.Equals(x_d, d),
                    mgr.Equals(x_log, mgr.Plus(log, ints[1])))))

    # transition relation.
    trans = mgr.And(cfg, labels)

    # fairness.
    fairness = mgr.Not(pcend)

    return symbols, init, trans, fairness
