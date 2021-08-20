from typing import Tuple, FrozenSet

from pysmt.environment import Environment as PysmtEnv
from pysmt.fnode import FNode
import pysmt.typing as types

from hint import Hint, Location
from utils import symb_to_next


def transition_system(env: PysmtEnv) -> Tuple[FrozenSet[FNode],
                                              FNode, FNode, FNode]:
    assert isinstance(env, PysmtEnv)
    mgr = env.formula_manager
    pc = mgr.Symbol("pc", types.INT)
    a_lst = [mgr.Symbol("a{}".format(i), types.INT) for i in range(1048)]
    x_pc = symb_to_next(mgr, pc)
    x_a_lst = [symb_to_next(mgr, a) for a in a_lst]

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


def hints(env: PysmtEnv) -> FrozenSet[Hint]:
    assert isinstance(env, PysmtEnv)

    mgr = env.formula_manager
    pc = mgr.Symbol("pc", types.INT)
    a_lst = [mgr.Symbol("a{}".format(i), types.INT) for i in range(1048)]
    symbs = frozenset([pc] + a_lst)

    a2 = a_lst[2]
    x_a2 = symb_to_next(mgr, a2)

    i_0 = mgr.Int(0)
    i_1 = mgr.Int(1)
    stutter = mgr.Equals(x_a2, a2)
    l0 = Location(env, mgr.Equals(a2, i_1), mgr.TRUE(), stutterT=stutter)
    l1 = Location(env, mgr.Equals(a2, i_0), mgr.TRUE(), stutterT=stutter)

    l0.set_progress(1, eq_0=mgr.Equals(x_a2, mgr.Minus(a2, i_1)))
    l1.set_progress(0, eq_0=mgr.Equals(x_a2, i_1))

    h_a2 = Hint("h_a2", env, frozenset([a2]), symbs)
    h_a2.set_locs([l0, l1])

    return frozenset([h_a2])
