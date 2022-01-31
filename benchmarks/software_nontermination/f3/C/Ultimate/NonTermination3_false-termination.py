from typing import Tuple, FrozenSet
from pysmt.environment import Environment as PysmtEnv
from pysmt.fnode import FNode
import pysmt.typing as types

from expr_utils import symb2next


def transition_system(env: PysmtEnv) -> Tuple[FrozenSet[FNode], FNode, FNode, FNode]:
    assert isinstance(env, PysmtEnv)
    mgr = env.formula_manager
    pc = mgr.Symbol("pc", types.INT)
    x_pc = symb2next(env, pc)
    i = mgr.Symbol("i", types.INT)
    x_i = symb2next(env, i)
    a = [mgr.Symbol("a{}".format(n), types.INT) for n in range(10)]
    x_a = [symb2next(env, _a) for _a in a]

    symbols = frozenset([pc, i, *a])

    m_1 = mgr.Int(-1)

    ints = [mgr.Int(idx) for idx in range(11)]
    pcs = []
    x_pcs = []
    n_locs = 3
    for idx in range(n_locs):
        num = ints[idx]
        pcs.append(mgr.Equals(pc, num))
        x_pcs.append(mgr.Equals(x_pc, num))
    pcend = mgr.Equals(pc, m_1)
    x_pcend = mgr.Equals(x_pc, m_1)

    ai_ge_0 = [mgr.Implies(mgr.Equals(i, ints[idx]), mgr.GE(a[idx], ints[0]))
               for idx in range(10)]
    ai_ge_0 = mgr.And(ai_ge_0)

    init = pcs[0]
    cfg = []
    # pc = 0 & 0 <= i < 10 & a[i] >= 0 -> pc' = 1
    cond = mgr.And(ai_ge_0, mgr.LE(ints[0], i), mgr.LT(i, ints[10]))
    cfg.append(mgr.Implies(mgr.And(pcs[0], cond), x_pcs[1]))
    # pc = 0 & !(0 <= i < 10 & a[i] >= 0) -> pc' = -1
    cfg.append(mgr.Implies(mgr.And(pcs[0], mgr.Not(cond)), x_pcend))
    # pc = 1 -> pc' = 2
    cfg.append(mgr.Implies(pcs[1], x_pcs[2]))
    # pc = 2 -> pc' = 0
    cfg.append(mgr.Implies(pcs[2], x_pcs[0]))
    # pc = -1 -> pc' = -1
    cfg.append(mgr.Implies(pcend, x_pcend))

    xa_eq_a = [mgr.Equals(_x_a, _a) for _a, _x_a in zip(a, x_a)]
    xa_eq_a = mgr.And(xa_eq_a)
    trans = []
    # pc = 0 -> a' = a & i' = i
    trans.append(mgr.Implies(pcs[0], mgr.And(xa_eq_a, mgr.Equals(x_i, i))))
    # pc = 1 -> a' = a
    trans.append(mgr.Implies(pcs[1], xa_eq_a))
    # pc = 2 -> a'[i] = 0
    xa_i_eq_0 = [mgr.Implies(mgr.Equals(i, ints[idx]),
                             mgr.Equals(x_a[idx], ints[0]))
                 for idx in range(10)]
    trans.append(mgr.Implies(pcs[2], mgr.And(xa_i_eq_0)))
    # pc = end -> a' = a & i' = i
    trans.append(mgr.Implies(pcend, mgr.And(xa_eq_a, mgr.Equals(x_i, i))))

    trans = mgr.And(*cfg, *trans)

    fairness = mgr.Not(mgr.Equals(pc, m_1))
    return symbols, init, trans, fairness
