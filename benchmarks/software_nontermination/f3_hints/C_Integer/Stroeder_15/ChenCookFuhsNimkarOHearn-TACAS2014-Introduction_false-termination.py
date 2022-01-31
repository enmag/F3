from typing import Tuple, FrozenSet

from pysmt.environment import Environment as PysmtEnv
from pysmt.fnode import FNode
import pysmt.typing as types

from expr_utils import symb2next
from hint import Hint, Location


def transition_system(env: PysmtEnv) -> Tuple[FrozenSet[FNode], FNode, FNode,
                                              FNode]:
    assert isinstance(env, PysmtEnv)
    mgr = env.formula_manager
    pc = mgr.Symbol("pc", types.INT)
    k = mgr.Symbol("k", types.INT)
    i = mgr.Symbol("i", types.INT)
    x_pc = symb2next(env, pc)
    x_k = symb2next(env, k)
    x_i = symb2next(env, i)

    symbols = frozenset([pc, k, i])

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
    # pc = 0 & k >= 0 -> pc' = 2
    cond = mgr.GE(k, ints[0])
    cfg.append(mgr.Implies(mgr.And(pcs[0], cond), x_pcs[2]))
    # pc = 0 & !(k >= 0) -> pc' = 1
    cfg.append(mgr.Implies(mgr.And(pcs[0], mgr.Not(cond)), x_pcs[1]))
    # pc = 1 -> pc' = 2
    cfg.append(mgr.Implies(pcs[1], x_pcs[2]))
    # pc = 2 & (i >= 0) -> pc' = 3
    cond = mgr.GE(i, ints[0])
    cfg.append(mgr.Implies(mgr.And(pcs[2], cond), x_pcs[3]))
    # pc = 2 & !(i >= 0) -> pc' = 4
    cfg.append(mgr.Implies(mgr.And(pcs[2], mgr.Not(cond)), x_pcs[4]))
    # pc = 3 -> pc' = 2
    cfg.append(mgr.Implies(pcs[3], x_pcs[2]))
    # pc = 4 -> pc' = -1
    cfg.append(mgr.Implies(pcs[4], x_pcend))
    # pc = -1 -> pc' = -1
    cfg.append(mgr.Implies(pcend, x_pcend))

    trans = []
    same_k = mgr.Equals(x_k, k)
    same_i = mgr.Equals(x_i, i)
    same = mgr.And(same_k, same_i)
    # pc = 0 -> same
    trans.append(mgr.Implies(pcs[0], same))
    # pc = 1 -> same_k & i' = i - 1
    trans.append(mgr.Implies(pcs[1],
                             mgr.And(same_k,
                                     mgr.Equals(x_i, mgr.Minus(i, ints[1])))))
    # pc = 2 -> same
    trans.append(mgr.Implies(pcs[2], same))
    # pc = 3 -> same_k
    trans.append(mgr.Implies(pcs[3], same_k))
    # pc = 4 -> same_k & i' = 2
    trans.append(mgr.Implies(pcs[4], mgr.And(same_k,
                                             mgr.Equals(x_i, ints[2]))))
    # pc = end -> same
    trans.append(mgr.Implies(pcend, same))

    trans = mgr.And(*cfg, *trans)

    fairness = mgr.Not(mgr.Equals(pc, m_1))

    return symbols, init, trans, fairness


def hints(env: PysmtEnv) -> FrozenSet[Hint]:
    assert isinstance(env, PysmtEnv)

    mgr = env.formula_manager
    pc = mgr.Symbol("pc", types.INT)
    k = mgr.Symbol("k", types.INT)
    i = mgr.Symbol("i", types.INT)

    symbs = frozenset([pc, k, i])

    x_i = symb2next(env, i)

    i_0 = mgr.Int(0)
    stutter = mgr.Equals(x_i, i)
    loc = Location(env, mgr.Equals(i, i_0), stutterT=stutter)
    loc.set_progress(0, mgr.Equals(x_i, i_0))
    h_i = Hint("h_i", env, frozenset([i]), symbs)
    h_i.set_locs([loc])

    return frozenset([h_i])
