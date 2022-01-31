from typing import Tuple, FrozenSet
from typing import Tuple, FrozenSet
from pysmt.environment import Environment as PysmtEnv
from pysmt.fnode import FNode
import pysmt.typing as types

from expr_utils import symb2next


def transition_system(env: PysmtEnv) -> Tuple[FrozenSet[FNode],
                                              FNode, FNode, FNode]:
    assert isinstance(env, PysmtEnv)
    mgr = env.formula_manager
    pc = mgr.Symbol("pc", types.INT)
    a_lst = [mgr.Symbol("a{}".format(i), types.INT) for i in range(1048)]
    x_pc = symb2next(env, pc)
    x_a_lst = [symb2next(env, a) for a in a_lst]

    m_1 = mgr.Int(-1)
    i_0 = mgr.Int(0)
    i_1 = mgr.Int(1)
    i_2 = mgr.Int(2)

    pc0 = mgr.Equals(pc, i_0)
    x_pc0 = mgr.Equals(x_pc, i_0)
    pc1 = mgr.Equals(pc, i_1)
    x_pc1 = mgr.Equals(x_pc, i_1)
    pc2 = mgr.Equals(pc, i_2)
    x_pc2 = mgr.Equals(x_pc, i_2)
    pcend = mgr.Equals(pc, m_1)
    x_pcend = mgr.Equals(x_pc, m_1)

    x_a_eq_a = mgr.And([mgr.Equals(x_a, a)
                        for a, x_a in zip(a_lst, x_a_lst)])

    init = pc0
    cfg = []
    # pc = 0 & a[2] > 0 -> pc = 1
    cfg.append(mgr.Implies(mgr.And(pc0, mgr.GE(a_lst[2], i_0)), x_pc1))
    # pc = 0 & !(a[2] > 0) -> pc = -1
    cfg.append(mgr.Implies(mgr.And(pc0, mgr.Not(mgr.GE(a_lst[2], i_0))),
                           x_pcend))
    # pc = 1 -> pc' = 2
    cfg.append(mgr.Implies(pc1, x_pc2))
    # pc = 2 -> pc' = 0
    cfg.append(mgr.Implies(pc2, x_pc0))
    # pc = -1 -> pc' = -1
    cfg.append(mgr.Implies(pcend, x_pcend))

    trans = []
    # pc = 0 -> a' = a
    trans.append(mgr.Implies(pc0, x_a_eq_a))
    # pc = 1 -> a[2]' = a[2] - 1
    trans.append(mgr.Implies(pc1, mgr.Equals(x_a_lst[2],
                                             mgr.Minus(a_lst[2], i_1))))
    # pc = end -> a' = a
    trans.append(mgr.Implies(pcend, x_a_eq_a))

    trans = mgr.And(*cfg, *trans)

    fairness = mgr.Not(mgr.Equals(pc, m_1))
    symbols = frozenset([pc] + a_lst)
    return symbols, init, trans, fairness
