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
    y1 = mgr.Symbol("y1", types.INT)
    x_y1 = symb2next(env, y1)
    y2 = mgr.Symbol("y2", types.INT)
    x_y2 = symb2next(env, y2)

    symbols = frozenset([pc, y1, y2])

    m_1 = mgr.Int(-1)

    n_locs = 5
    max_int = n_locs
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
    # pc = 0 & y1 >= 0 & y2 >= 0 -> pc' = 1
    cond = mgr.And(mgr.GE(y1, ints[0]), mgr.GE(y2, ints[0]))
    cfg.append(mgr.Implies(mgr.And(pcs[0], cond), x_pcs[1]))
    # pc = 0 & !(y1 >= 0 & y2 >= 0) -> pc' = -1
    cfg.append(mgr.Implies(mgr.And(pcs[0], mgr.Not(cond)), x_pcend))
    # pc = 1 & y1 != y2 -> pc' = 2
    cond = mgr.Not(mgr.Equals(y1, y2))
    cfg.append(mgr.Implies(mgr.And(pcs[1], cond), x_pcs[2]))
    # pc = 1 & !(y1 != y2) -> pc' = -1
    cfg.append(mgr.Implies(mgr.And(pcs[1], mgr.Not(cond)), x_pcend))
    # pc = 2 & y1 > y2 -> pc' = 3
    cond = mgr.GT(y1, y2)
    cfg.append(mgr.Implies(mgr.And(pcs[2], cond), x_pcs[3]))
    # pc = 2 & !(y1 > y2) -> pc' = 4
    cfg.append(mgr.Implies(mgr.And(pcs[2], mgr.Not(cond)), x_pcs[4]))
    # pc = 3 -> pc' = 1
    cfg.append(mgr.Implies(pcs[3], x_pcs[1]))
    # pc = 4 -> pc' = 1
    cfg.append(mgr.Implies(pcs[4], x_pcs[1]))
    # pc = -1 -> pc' = -1
    cfg.append(mgr.Implies(pcend, x_pcend))

    trans = []
    same_y1 = mgr.Equals(x_y1, y1)
    same_y2 = mgr.Equals(x_y2, y2)
    same = mgr.And(same_y1, same_y2)
    # pc = 0 -> same
    trans.append(mgr.Implies(pcs[0], same))
    # pc = 1 -> same
    trans.append(mgr.Implies(pcs[1], same))
    # pc = 2 -> same
    trans.append(mgr.Implies(pcs[2], same))
    # pc = 3 -> y1' = y1 - y2 & same_y2
    trans.append(mgr.Implies(pcs[3], mgr.And(mgr.Equals(x_y1,
                                                        mgr.Minus(y1, y2)),
                                             same_y2)))
    # pc = 4 -> same_y1 & y2' = y2 - y1
    trans.append(mgr.Implies(pcs[4], mgr.And(same_y1,
                                             mgr.Equals(x_y2,
                                                        mgr.Minus(y2, y1)))))
    # pc = end -> same
    trans.append(mgr.Implies(pcend, same))

    trans = mgr.And(*cfg, *trans)

    fairness = mgr.Not(mgr.Equals(pc, m_1))
    return symbols, init, trans, fairness
