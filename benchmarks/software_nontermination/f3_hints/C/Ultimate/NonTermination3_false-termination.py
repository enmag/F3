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
    i = mgr.Symbol("i", types.INT)
    x_i = symb_to_next(mgr, i)
    a = [mgr.Symbol("a{}".format(n), types.INT) for n in range(10)]
    x_a = [symb_to_next(mgr, _a) for _a in a]

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


def hints(env: PysmtEnv) -> FrozenSet[Hint]:
    assert isinstance(env, PysmtEnv)

    mgr = env.formula_manager
    pc = mgr.Symbol("pc", types.INT)
    i = mgr.Symbol("i", types.INT)
    a = [mgr.Symbol("a{}".format(n), types.INT) for n in range(10)]
    symbs = frozenset([pc, i, *a])

    x_i = symb_to_next(mgr, i)
    a0 = a[0]
    x_a0 = symb_to_next(mgr, a0)

    i_0 = mgr.Int(0)

    stutter = mgr.Equals(x_i, i)
    l0 = Location(env, mgr.Equals(i, i_0), mgr.TRUE(), stutterT=stutter)
    l0.set_progress(0, mgr.Equals(x_i, i_0))
    h_i = Hint("h_i", env, frozenset([i]), symbs)
    h_i.set_locs([l0])

    stutter = mgr.Equals(x_a0, a0)
    l0 = Location(env, mgr.Equals(a0, i_0), mgr.TRUE(), stutterT=stutter)
    l0.set_progress(0, mgr.Equals(x_a0, i_0))
    h_a0 = Hint("h_a0", env, frozenset([a0]), symbs)
    h_a0.set_locs([l0])

    return frozenset([h_i, h_a0])
