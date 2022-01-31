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
    x = mgr.Symbol("x", types.INT)
    y = mgr.Symbol("y", types.INT)
    z = mgr.Symbol("z", types.INT)
    x_pc = symb2next(env, pc)
    x_x = symb2next(env, x)
    x_y = symb2next(env, y)
    x_z = symb2next(env, z)

    symbols = frozenset([pc, x, y, z])

    m_1 = mgr.Int(-1)

    n_locs = 4
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
    # pc = 1 -> pc' = 2
    cfg.append(mgr.Implies(pcs[1], x_pcs[2]))
    # pc = 2 -> pc' = 3
    cfg.append(mgr.Implies(pcs[2], x_pcs[3]))
    # pc = 3 -> pc' = 0
    cfg.append(mgr.Implies(pcs[3], x_pcs[0]))
    # pc = -1 -> pc' = -1
    cfg.append(mgr.Implies(pcend, x_pcend))

    trans = []
    same_x = mgr.Equals(x_x, x)
    same_y = mgr.Equals(x_y, y)
    same_z = mgr.Equals(x_z, z)
    same = mgr.And(same_x, same_y, same_z)

    # pc = 0 -> same
    trans.append(mgr.Implies(pcs[0], same))
    # pc = 1 -> x' = x + y & same_y & same_z
    trans.append(mgr.Implies(pcs[1],
                             mgr.And(mgr.Equals(x_x, mgr.Plus(x, y)),
                                     same_y, same_z)))
    # pc = 2 -> same_x & y' = y + z & same_z
    trans.append(mgr.Implies(pcs[2],
                             mgr.And(same_x,
                                     mgr.Equals(x_y, mgr.Plus(y, z)),
                                     same_z)))
    # pc = 3 -> same_x & same_y & z' = z + 1
    trans.append(mgr.Implies(pcs[3],
                             mgr.And(same_x, same_y,
                                     mgr.Equals(x_z, mgr.Plus(z, x)))))
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
    y = mgr.Symbol("y", types.INT)
    z = mgr.Symbol("z", types.INT)
    symbs = frozenset([pc, x, y, z])

    i_0 = mgr.Int(0)

    x_x = symb2next(env, x)
    stutter = mgr.Equals(x_x, x)
    loc = Location(env, mgr.GT(x, i_0), mgr.GE(y, i_0), stutterT=stutter)
    loc.set_progress(0, mgr.Equals(x_x, mgr.Plus(x, y)))
    h_x = Hint("h_x", env, frozenset([x]), symbs)
    h_x.set_locs([loc])

    x_y = symb2next(env, y)
    stutter = mgr.Equals(x_y, y)
    loc = Location(env, mgr.GE(y, i_0), mgr.GE(z, i_0), stutterT=stutter)
    loc.set_progress(0, mgr.Equals(x_y, mgr.Plus(y, z)))
    h_y = Hint("h_y", env, frozenset([y]), symbs)
    h_y.set_locs([loc])

    x_z = symb2next(env, z)
    stutter = mgr.Equals(x_z, z)
    loc = Location(env, mgr.GE(z, i_0), mgr.GE(x, i_0), stutterT=stutter)
    loc.set_progress(0, mgr.Equals(x_z, mgr.Plus(z, x)))
    h_z = Hint("h_z", env, frozenset([z]), symbs)
    h_z.set_locs([loc])

    return frozenset([h_x, h_y, h_z])
