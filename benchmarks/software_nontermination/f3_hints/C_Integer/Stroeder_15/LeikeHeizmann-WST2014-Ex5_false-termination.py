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
    a = mgr.Symbol("a", types.INT)
    b = mgr.Symbol("b", types.INT)
    olda = mgr.Symbol("olda", types.INT)
    x_pc = symb2next(env, pc)
    x_a = symb2next(env, a)
    x_b = symb2next(env, b)
    x_olda = symb2next(env, olda)

    symbols = frozenset([pc, a, b, olda])

    m_1 = mgr.Int(-1)

    n_locs = 4
    max_int = 8
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
    # pc = 0 & (a >= 7) -> pc' = 1
    cond = mgr.GE(a, ints[7])
    cfg.append(mgr.Implies(mgr.And(pcs[0], cond), x_pcs[1]))
    # pc = 0 & !(a >= 7) -> pc' = -1
    cfg.append(mgr.Implies(mgr.And(pcs[0], mgr.Not(cond)), x_pcend))
    # pc = 1 -> pc' = 2
    cfg.append(mgr.Implies(pcs[1], x_pcs[2]))
    # pc = 2 -> pc' = 3
    cfg.append(mgr.Implies(pcs[2], x_pcs[3]))
    # pc = 3 -> pc' = 0
    cfg.append(mgr.Implies(pcs[3], x_pcs[0]))
    # pc = -1 -> pc' = -1
    cfg.append(mgr.Implies(pcend, x_pcend))

    trans = []
    same_a = mgr.Equals(x_a, a)
    same_b = mgr.Equals(x_b, b)
    same_olda = mgr.Equals(x_olda, olda)
    same = mgr.And(same_a, same_b, same_olda)

    # pc = 0 -> same
    trans.append(mgr.Implies(pcs[0], same))
    # pc = 1 -> same_a & same_b & olda' = a
    trans.append(mgr.Implies(pcs[1],
                             mgr.And(same_a, same_b, mgr.Equals(x_olda, a))))
    # pc = 2 -> a' = b & same_b & same_olda
    trans.append(mgr.Implies(pcs[2],
                             mgr.And(mgr.Equals(x_a, b),
                                     same_b, same_olda)))
    # pc = 3 -> same_a & b' = olda + 1 & same_olda
    trans.append(mgr.Implies(pcs[3],
                             mgr.And(same_a,
                                     mgr.Equals(x_b, mgr.Plus(olda, ints[1])),
                                     same_olda)))
    # pc = end -> same
    trans.append(mgr.Implies(pcend, same))

    trans = mgr.And(*cfg, *trans)

    fairness = mgr.Not(mgr.Equals(pc, m_1))

    return symbols, init, trans, fairness


def hints(env: PysmtEnv) -> FrozenSet[Hint]:
    assert isinstance(env, PysmtEnv)

    mgr = env.formula_manager
    pc = mgr.Symbol("pc", types.INT)
    a = mgr.Symbol("a", types.INT)
    b = mgr.Symbol("b", types.INT)
    olda = mgr.Symbol("olda", types.INT)

    symbs = frozenset([pc, a, b, olda])

    i_1 = mgr.Int(1)
    i_7 = mgr.Int(7)

    x_a = symb2next(env, a)
    stutter = mgr.Equals(x_a, a)
    loc = Location(env, mgr.GE(a, i_7), mgr.GE(b, i_7),
                   stutterT=stutter)
    loc.set_progress(0, mgr.Equals(x_a, b))
    h_a = Hint("h_a", env, frozenset([a]), symbs)
    h_a.set_locs([loc])

    x_b = symb2next(env, b)
    stutter = mgr.Equals(x_b, b)
    loc = Location(env, mgr.GE(b, i_7), mgr.GE(olda, i_7),
                   stutterT=stutter)
    loc.set_progress(0, mgr.Equals(x_b, mgr.Plus(olda, i_1)))
    h_b = Hint("h_b", env, frozenset([b]), symbs)
    h_b.set_locs([loc])

    x_olda = symb2next(env, olda)
    stutter = mgr.Equals(x_olda, olda)
    loc = Location(env, mgr.GE(olda, i_7), mgr.GE(a, i_7),
                   stutterT=stutter)
    loc.set_progress(0, mgr.Equals(x_olda, a))
    h_olda = Hint("h_olda", env, frozenset([olda]), symbs)
    h_olda.set_locs([loc])

    return frozenset([h_a, h_b, h_olda])
