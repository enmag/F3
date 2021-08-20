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
    x = mgr.Symbol("x", types.INT)
    x_pc = symb_to_next(mgr, pc)
    x_x = symb_to_next(mgr, x)

    symbols = frozenset([pc, x])

    m_1 = mgr.Int(-1)

    n_locs = 3
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
    # pc = 0 & (x > 0) -> pc' = 1
    cond = mgr.GT(x, ints[0])
    cfg.append(mgr.Implies(mgr.And(pcs[0], cond), x_pcs[1]))
    # pc = 0 & !(x > 0) -> pc' = -1
    cfg.append(mgr.Implies(mgr.And(pcs[0], mgr.Not(cond)), x_pcend))
    # pc = 1 & (x != 0) -> pc' = 2
    cond = mgr.Not(mgr.Equals(x, ints[0]))
    cfg.append(mgr.Implies(mgr.And(pcs[1], cond), x_pcs[2]))
    # pc = 1 & !(x != 0) -> pc' = -1
    cfg.append(mgr.Implies(mgr.And(pcs[1], mgr.Not(cond)), x_pcend))
    # pc = 2 -> pc' = 1
    cfg.append(mgr.Implies(pcs[2], x_pcs[1]))
    # pc = -1 -> pc' = -1
    cfg.append(mgr.Implies(pcend, x_pcend))

    trans = []
    same = mgr.Equals(x_x, x)

    # pc = 0 -> same
    trans.append(mgr.Implies(pcs[0], same))
    # pc = 1 -> same
    trans.append(mgr.Implies(pcs[1], same))
    # pc = 2 -> x' = x - 2
    trans.append(mgr.Implies(pcs[2],
                             mgr.Equals(x_x, mgr.Minus(x, ints[2]))))
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

    i_0 = mgr.Int(0)
    i_2 = mgr.Int(2)

    x_x = symb_to_next(mgr, x)
    stutter = mgr.Equals(x_x, x)
    loc = Location(env, mgr.LT(x, i_0), stutterT=stutter)
    loc.set_progress(0, eq_0=mgr.Equals(x_x, mgr.Minus(x, i_2)))
    h_x = Hint("h_x", env, frozenset([x]), symbs)
    h_x.set_locs([loc])

    return frozenset([h_x])
