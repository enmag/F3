from typing import Tuple, FrozenSet

from pysmt.environment import Environment as PysmtEnv
from pysmt.fnode import FNode
import pysmt.typing as types

from utils import symb_to_next
from hint import Hint, Location


def transition_system(env: PysmtEnv) -> Tuple[FrozenSet[FNode], FNode, FNode,
                                              FNode]:
    assert isinstance(env, PysmtEnv)
    mgr = env.formula_manager
    pc = mgr.Symbol("pc", types.INT)
    x_pc = symb_to_next(mgr, pc)
    x = mgr.Symbol("x", types.INT)
    x_x = symb_to_next(mgr, x)

    symbols = frozenset([pc, x])

    m_1 = mgr.Int(-1)

    n_locs = 9
    ints = [mgr.Int(idx) for idx in range(9)]
    pcs = []
    x_pcs = []
    for idx in range(n_locs):
        num = ints[idx]
        pcs.append(mgr.Equals(pc, num))
        x_pcs.append(mgr.Equals(x_pc, num))
    pcend = mgr.Equals(pc, m_1)
    x_pcend = mgr.Equals(x_pc, m_1)

    init = pcs[0]
    cfg = []
    # pc = 0 & x >= 0 -> pc' = 1
    cfg.append(mgr.Implies(mgr.And(pcs[0], mgr.GE(x, ints[0])),
                           x_pcs[1]))
    # pc = 0 & !(x >= 0) -> pc' = -1
    cfg.append(mgr.Implies(mgr.And(pcs[0], mgr.Not(mgr.GE(x, ints[0]))),
                           x_pcend))
    # pc = 1 -> pc' = 2 | pc' = 3
    cfg.append(mgr.Implies(pcs[1], mgr.Or(x_pcs[2], x_pcs[3])))
    # pc = 2 -> pc' = 0
    cfg.append(mgr.Implies(pcs[2], x_pcs[0]))
    # pc = 3 -> pc' = 4 | pc' = 5
    cfg.append(mgr.Implies(pcs[3], mgr.Or(x_pcs[4], x_pcs[5])))
    # pc = 4 -> pc' = 0
    cfg.append(mgr.Implies(pcs[4], x_pcs[0]))
    # pc = 5 -> pc' = 6 | pc' = 7
    cfg.append(mgr.Implies(pcs[5], mgr.Or(x_pcs[6], x_pcs[7])))
    # pc = 6 -> pc' = 0
    cfg.append(mgr.Implies(pcs[6], x_pcs[0]))
    # pc = 7 -> pc' = 8 | pc' = -1
    cfg.append(mgr.Implies(pcs[7], mgr.Or(x_pcs[8], x_pcend)))
    # pc = 8 -> pc' = 0
    cfg.append(mgr.Implies(pcs[8], x_pcs[0]))
    # pc = -1 -> pc' = -1
    cfg.append(mgr.Implies(pcend, x_pcend))

    trans = []
    same = mgr.Equals(x_x, x)
    # pc = 0 -> x' = x
    trans.append(mgr.Implies(pcs[0], same))
    # pc = 1 -> x' = x
    trans.append(mgr.Implies(pcs[1], same))
    # pc = 2 -> x' = x + 1
    trans.append(mgr.Implies(pcs[2], mgr.Equals(x_x, mgr.Plus(x, ints[1]))))
    # pc = 3 -> x' = x
    trans.append(mgr.Implies(pcs[3], same))
    # pc = 4 -> x' = x + 2
    trans.append(mgr.Implies(pcs[4], mgr.Equals(x_x, mgr.Plus(x, ints[2]))))
    # pc = 5 -> x' = x
    trans.append(mgr.Implies(pcs[5], same))
    # pc = 6 -> x' = x
    trans.append(mgr.Implies(pcs[6], mgr.Equals(x_x, mgr.Plus(x, ints[3]))))
    # pc = 7 -> x' = x
    trans.append(mgr.Implies(pcs[7], same))
    # pc = 8 -> x' = x
    trans.append(mgr.Implies(pcs[8], mgr.Equals(x_x, mgr.Plus(x, ints[4]))))
    # pc = end -> same
    trans.append(mgr.Implies(pcend, same))

    trans = mgr.And(*cfg, *trans)

    fairness = mgr.Not(mgr.Equals(pc, m_1))
    return symbols, init, trans, fairness


def hints(env: PysmtEnv) -> FrozenSet[Hint]:
    assert isinstance(env, PysmtEnv)

    mgr = env.formula_manager
    pc = mgr.Symbol("pc", types.INT)
    x = mgr.Symbol("x", types.INT)
    symbs = frozenset([pc, x])

    x_x = symb_to_next(mgr, x)
    i_1 = mgr.Int(1)
    stutter = mgr.Equals(x_x, x)
    l0 = Location(env, mgr.GE(x, i_1), mgr.TRUE(), stutterT=stutter)
    l0.set_progress(0, eq_0=mgr.Equals(x_x, mgr.Plus(x, i_1)))
    h_x = Hint("h_x", env, frozenset([x]), symbs)
    h_x.set_locs([l0])

    return frozenset([h_x])
