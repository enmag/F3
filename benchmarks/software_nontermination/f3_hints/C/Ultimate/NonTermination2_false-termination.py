from typing import FrozenSet, Tuple

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
    old_x = mgr.Symbol("old_x", types.INT)
    x_old_x = symb_to_next(mgr, old_x)

    symbols = frozenset([pc, x, old_x])

    m_1 = mgr.Int(-1)
    i_1 = mgr.Int(1)
    i_2 = mgr.Int(2)

    ints = []
    pcs = []
    x_pcs = []
    n_locs = 4
    for idx in range(n_locs):
        num = mgr.Int(idx)
        ints.append(num)
        pcs.append(mgr.Equals(pc, num))
        x_pcs.append(mgr.Equals(x_pc, num))
    pcend = mgr.Equals(pc, m_1)
    x_pcend = mgr.Equals(x_pc, m_1)

    init = pcs[0]
    cfg = []
    # pc = 0 & x > 1 -> pc' = 1
    cfg.append(mgr.Implies(mgr.And(pcs[0], mgr.GT(x, i_1)), x_pcs[1]))
    # pc = 0 & !(x > 1) -> pc' = -1
    cfg.append(mgr.Implies(mgr.And(pcs[0], mgr.Not(mgr.GT(x, i_1))), x_pcend))
    # pc = 1 -> pc' = 2
    cfg.append(mgr.Implies(pcs[1], x_pcs[2]))
    # pc = 2 -> pc' = 3
    cfg.append(mgr.Implies(pcs[2], x_pcs[3]))
    # pc = 3 & x < 2 * old_x -> pc' = -1
    cfg.append(mgr.Implies(mgr.And(pcs[3], mgr.LT(x, mgr.Times(old_x, i_2))),
                           x_pcend))
    # pc = 3 & !(x < 2 * old_x) -> pc' = 0
    cfg.append(mgr.Implies(mgr.And(pcs[3],
                                   mgr.Not(mgr.LT(x, mgr.Times(old_x, i_2)))),
                           x_pcs[0]))
    # pc = -1 -> pc' = -1
    cfg.append(mgr.Implies(pcend, x_pcend))

    trans = []
    same = mgr.And(mgr.Equals(x_x, x), mgr.Equals(x_old_x, old_x))
    # pc = 0 -> x' = x & old_x' = old_x
    trans.append(mgr.Implies(pcs[0], same))
    # pc = 1 -> x' = x & old_x' = x
    trans.append(mgr.Implies(pcs[1], mgr.And(mgr.Equals(x_x, x),
                                             mgr.Equals(x_old_x, x))))
    # pc = 2 -> old_x' = old_x
    trans.append(mgr.Implies(pcs[2], mgr.Equals(x_old_x, old_x)))
    # pc = 3 -> x' = x & old_x' = old_x
    trans.append(mgr.Implies(pcs[3], same))
    # pc = end -> x' = x
    trans.append(mgr.Implies(pcend, same))

    trans = mgr.And(*cfg, *trans)

    fairness = mgr.Not(mgr.Equals(pc, m_1))
    return symbols, init, trans, fairness


def hints(env: PysmtEnv) -> FrozenSet[Hint]:
    assert isinstance(env, PysmtEnv)

    mgr = env.formula_manager
    pc = mgr.Symbol("pc", types.INT)
    x = mgr.Symbol("x", types.INT)
    old_x = mgr.Symbol("old_x", types.INT)
    symbs = frozenset([pc, x, old_x])

    x_x = symb_to_next(mgr, x)

    i_1 = mgr.Int(1)
    i_2 = mgr.Int(2)
    stutter = mgr.Equals(x_x, x)
    l0 = Location(env, mgr.GT(x, i_1), mgr.TRUE(), stutterT=stutter)
    l0.set_progress(0, eq_0=mgr.Equals(x_x, mgr.Plus(mgr.Times(x, i_2), i_1)))

    h_x = Hint("h_x", env, frozenset([x]), symbs)
    h_x.set_locs([l0])

    return frozenset([h_x])
