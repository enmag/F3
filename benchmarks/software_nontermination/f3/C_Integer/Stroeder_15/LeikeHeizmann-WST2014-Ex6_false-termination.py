from typing import Tuple, FrozenSet
from pysmt.environment import Environment as PysmtEnv
from pysmt.fnode import FNode
import pysmt.typing as types

from expr_utils import symb2next


def transition_system(env: PysmtEnv) -> Tuple[FrozenSet[FNode], FNode, FNode, FNode]:
    assert isinstance(env, PysmtEnv)
    mgr = env.formula_manager
    pc = mgr.Symbol("pc", types.INT)
    a = mgr.Symbol("a", types.INT)
    b = mgr.Symbol("b", types.INT)
    x_pc = symb2next(env, pc)
    x_a = symb2next(env, a)
    x_b = symb2next(env, b)

    symbols = frozenset([pc, a, b])

    m_1 = mgr.Int(-1)

    n_locs = 3
    max_int = 4
    ints = []
    pcs = []
    x_pcs = []
    for idx in range(n_locs):
        num = mgr.Int(idx)
        ints.append(num)
        pcs.append(mgr.Equals(pc, num))
        x_pcs.append(mgr.Equals(x_pc, num))

    for idx in range(n_locs, max_int):
        num = mgr.Int(idx)
        ints.append(num)

    pcend = mgr.Equals(pc, m_1)
    x_pcend = mgr.Equals(x_pc, m_1)

    init = pcs[0]

    cfg = []
    # pc = 0 & (a >= 1 & b >= 1) -> pc' = 1
    cond = mgr.And(mgr.GE(a, ints[1]), mgr.GE(b, ints[1]))
    cfg.append(mgr.Implies(mgr.And(pcs[0], cond), x_pcs[1]))
    # pc = 0 & !(a >= 1 & b >= 1) -> pc' = -1
    cfg.append(mgr.Implies(mgr.And(pcs[0], mgr.Not(cond)), x_pcend))
    # pc = 1 -> pc' = 2
    cfg.append(mgr.Implies(pcs[1], x_pcs[2]))
    # pc = 2 -> pc' = 0
    cfg.append(mgr.Implies(pcs[2], x_pcs[0]))
    # pc = -1 -> pc' = -1
    cfg.append(mgr.Implies(pcend, x_pcend))

    trans = []
    same_a = mgr.Equals(x_a, a)
    same_b = mgr.Equals(x_b, b)
    same = mgr.And(same_a, same_b)

    # pc = 0 -> same
    trans.append(mgr.Implies(pcs[0], same))
    # pc = 1 -> a' = 2a & same_b
    trans.append(mgr.Implies(pcs[1],
                             mgr.And(mgr.Equals(x_a, mgr.Times(ints[2], a)),
                                     same_b)))
    # pc = 2 -> same_a & b' = 3b
    trans.append(mgr.Implies(pcs[2],
                             mgr.And(same_a,
                                     mgr.Equals(x_b, mgr.Times(ints[3], b)))))
    # pc = end -> same
    trans.append(mgr.Implies(pcend, same))

    trans = mgr.And(*cfg, *trans)

    fairness = mgr.Not(mgr.Equals(pc, m_1))

    return symbols, init, trans, fairness
