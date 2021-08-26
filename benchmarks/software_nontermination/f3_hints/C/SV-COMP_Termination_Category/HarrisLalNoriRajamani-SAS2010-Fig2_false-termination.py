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
    fpc = mgr.Symbol("fpc", types.INT)
    x_fpc = symb_to_next(mgr, fpc)
    x = mgr.Symbol("x", types.INT)
    x_x = symb_to_next(mgr, x)
    y = mgr.Symbol("y", types.INT)
    x_y = symb_to_next(mgr, y)
    d = mgr.Symbol("d", types.INT)
    x_d = symb_to_next(mgr, d)

    symbols = frozenset([pc, fpc, x, y, d])

    m_1 = mgr.Int(-1)

    n_locs = 14
    n_flocs = 15
    max_int = 15
    ints = []
    pcs = []
    x_pcs = []
    for idx in range(n_locs):
        num = mgr.Int(idx)
        ints.append(num)
        pcs.append(mgr.Equals(pc, num))
        x_pcs.append(mgr.Equals(x_pc, num))

    for idx in range(n_locs, max_int + 1):
        num = mgr.Int(idx)
        ints.append(num)

    pcend = mgr.Equals(pc, m_1)
    x_pcend = mgr.Equals(x_pc, m_1)

    fpcs = []
    x_fpcs = []
    for idx in range(n_flocs):
        fpcs.append(mgr.Equals(fpc, ints[idx]))
        x_fpcs.append(mgr.Equals(x_fpc, ints[idx]))

    fpcend = mgr.Equals(fpc, m_1)
    x_fpcend = mgr.Equals(x_fpc, m_1)

    init = mgr.And(pcs[0], fpcend)
    cfg = []
    # pc = 0 -> pc' = 1 | pc' = 2
    cfg.append(mgr.Implies(pcs[0], mgr.Or(x_pcs[1], x_pcs[2])))
    # pc = 1 -> pc' = 2
    cfg.append(mgr.Implies(pcs[1], x_pcs[2]))
    # pc = 2 -> pc' = 3 | pc' = 4
    cfg.append(mgr.Implies(pcs[2], mgr.Or(x_pcs[3], x_pcs[4])))
    # pc = 3 & fpc != end -> pc' = 3
    cfg.append(mgr.Implies(mgr.And(pcs[2], mgr.Not(fpcend)), x_pcs[3]))
    # pc = 3 & fpc = end -> pc' = 4
    cfg.append(mgr.Implies(mgr.And(pcs[2], fpcend), x_pcs[4]))
    # pc = 4 -> pc' = 5 | pc' = 6
    cfg.append(mgr.Implies(pcs[4], mgr.Or(x_pcs[5], x_pcs[6])))
    # pc = 5 & fpc != end -> pc' = 5
    cfg.append(mgr.Implies(mgr.And(pcs[5], mgr.Not(fpcend)), x_pcs[5]))
    # pc = 5 & fpc = end -> pc' = 6
    cfg.append(mgr.Implies(mgr.And(pcs[5], fpcend), x_pcs[6]))
    # pc = 6 -> pc' = 7 | pc' = 8
    cfg.append(mgr.Implies(pcs[6], mgr.Or(x_pcs[7], x_pcs[8])))
    # pc = 7 & fpc != end -> pc' = 7
    cfg.append(mgr.Implies(mgr.And(pcs[7], mgr.Not(fpcend)), x_pcs[7]))
    # pc = 7 & fpc = end -> pc' = 8
    cfg.append(mgr.Implies(mgr.And(pcs[7], fpcend), x_pcs[8]))
    # pc = 8 -> pc' = 9 | pc' = 10
    cfg.append(mgr.Implies(pcs[8], mgr.Or(x_pcs[9], x_pcs[10])))
    # pc = 9 & fpc != end -> pc' = 9
    cfg.append(mgr.Implies(mgr.And(pcs[9], mgr.Not(fpcend)), x_pcs[9]))
    # pc = 9 & fpc = end -> pc' = 10
    cfg.append(mgr.Implies(mgr.And(pcs[9], fpcend), x_pcs[10]))
    # pc = 10 -> pc' = 11 | pc' = 12
    cfg.append(mgr.Implies(pcs[10], mgr.Or(x_pcs[11], x_pcs[12])))
    # pc = 11 -> pc' = 12
    cfg.append(mgr.Implies(pcs[11], x_pcs[12]))
    # pc = 12 & x > 0 -> pc' = 13
    cond = mgr.GT(x, ints[0])
    cfg.append(mgr.Implies(mgr.And(pcs[12], cond), x_pcs[13]))
    # pc = 12 & !(x > 0) -> pc' = -1
    cfg.append(mgr.Implies(mgr.And(pcs[12], mgr.Not(cond)), x_pcend))
    # pc = 13 -> pc = 12
    cfg.append(mgr.Implies(pcs[13], x_pcs[12]))
    # pc = -1 -> pc' = -1
    cfg.append(mgr.Implies(pcend, x_pcend))

    # pc = 2 & pc' = 3 -> fpc' = 0
    cfg.append(mgr.Implies(mgr.And(pcs[2], x_pcs[3]), x_fpcs[0]))
    # pc = 4 & pc' = 5 -> fpc' = 0
    cfg.append(mgr.Implies(mgr.And(pcs[4], x_pcs[5]), x_fpcs[0]))
    # pc = 6 & pc' = 7 -> fpc' = 0
    cfg.append(mgr.Implies(mgr.And(pcs[6], x_pcs[7]), x_fpcs[0]))
    # pc = 8 & pc' = 9 -> fpc' = 0
    cfg.append(mgr.Implies(mgr.And(pcs[8], x_pcs[9]), x_fpcs[0]))
    # fpc = 0 -> fpc' = 1 | fpc' = 8
    cfg.append(mgr.Implies(fpcs[0], mgr.Or(x_fpcs[1], x_fpcs[8])))
    # fpc = 1 -> fpc' = 2 | fpc' = 5
    cfg.append(mgr.Implies(fpcs[1], mgr.Or(x_fpcs[2], x_fpcs[5])))
    # fpc = 2 -> fpc' = 3 | fpc' = 4
    cfg.append(mgr.Implies(fpcs[2], mgr.Or(x_fpcs[3], x_fpcs[4])))
    # fpc = 3 -> fpc' = -1
    cfg.append(mgr.Implies(fpcs[3], x_fpcend))
    # fpc = 4 -> fpc' = -1
    cfg.append(mgr.Implies(fpcs[4], x_fpcend))
    # fpc = 5 -> fpc' = 6 | fpc' = 7
    cfg.append(mgr.Implies(fpcs[5], mgr.Or(x_fpcs[6], x_fpcs[7])))
    # fpc = 6 -> fpc' = -1
    cfg.append(mgr.Implies(fpcs[6], x_fpcend))
    # fpc = 7 -> fpc' = -1
    cfg.append(mgr.Implies(fpcs[7], x_fpcend))
    # fpc = 8 -> fpc' = 9 | fpc' = 12
    cfg.append(mgr.Implies(fpcs[8], mgr.Or(x_fpcs[9], x_fpcs[12])))
    # fpc = 9 -> fpc' = 10 | fpc' = 11
    cfg.append(mgr.Implies(fpcs[9], mgr.Or(x_fpcs[10], x_fpcs[11])))
    # fpc = 10 -> fpc' = -1
    cfg.append(mgr.Implies(fpcs[10], x_fpcend))
    # fpc = 11 -> fpc' = -1
    cfg.append(mgr.Implies(fpcs[11], x_fpcend))
    # fpc = 12 -> fpc' = 13 | fpc' = 14
    cfg.append(mgr.Implies(fpcs[12], mgr.Or(x_fpcs[13], x_fpcs[14])))
    # fpc = 13 -> fpc' = -1
    cfg.append(mgr.Implies(fpcs[10], x_fpcend))
    # fpc = 14 -> fpc' = -1
    cfg.append(mgr.Implies(fpcs[11], x_fpcend))
    # fpc = -1 & !(pc = 2 & pc' = 3) & !(pc = 4 & pc' = 5) &
    # !(pc = 6 & pc' = 7) & !(pc = 8 & pc' = 9) -> fpc' = -1
    cond = mgr.And(mgr.Not(mgr.And(pcs[2], x_pcs[3])),
                   mgr.Not(mgr.And(pcs[4], x_pcs[5])),
                   mgr.Not(mgr.And(pcs[6], x_pcs[7])),
                   mgr.Not(mgr.And(pcs[8], x_pcs[9])))
    cfg.append(mgr.Implies(mgr.And(fpcend, cond), x_fpcend))

    trans = []
    same_x = mgr.Equals(x_x, x)
    same_y = mgr.Equals(x_y, y)
    same_d = mgr.Equals(x_d, d)
    same_xd = mgr.And(same_x, same_d)
    same = mgr.And(same_x, same_y, same_d)
    # pc = 0 -> same_xd
    trans.append(mgr.Implies(pcs[0], same_xd))
    # pc = 1 -> same_x & d' = d - 1
    trans.append(mgr.Implies(pcs[1],
                             mgr.And(same_x,
                                     mgr.Equals(x_d, mgr.Minus(d, ints[1])))))
    # pc = [2..10] -> same_xd
    for idx in range(2, 11):
        trans.append(mgr.Implies(pcs[idx], same_xd))
    # pc = 11 -> same_x & d' = d - 1
    trans.append(mgr.Implies(pcs[11],
                             mgr.And(same_x,
                                     mgr.Equals(x_d, mgr.Minus(d, ints[1])))))
    # pc = 12 -> same_xd
    trans.append(mgr.Implies(pcs[12], same_xd))
    # pc = 13 -> x' = x - d & same_d
    trans.append(mgr.Implies(pcs[13], mgr.And(mgr.Equals(x_x, mgr.Minus(x, d)),
                                              same_d)))
    # pc = end -> same
    trans.append(mgr.Implies(pcend, same))

    # fpc = [0..2] -> same_y
    for idx in range(3):
        trans.append(mgr.Implies(fpcs[idx], same_y))
    # fpc = 3 -> y' = 0
    trans.append(mgr.Implies(fpcs[3], mgr.Equals(x_y, ints[0])))
    # fpc = 4 -> y' = 1
    trans.append(mgr.Implies(fpcs[4], mgr.Equals(x_y, ints[1])))
    # fpc = 5 -> same_y
    trans.append(mgr.Implies(fpcs[5], same_y))
    # fpc = 6 -> y' = 2
    trans.append(mgr.Implies(fpcs[6], mgr.Equals(x_y, ints[2])))
    # fpc = 7 -> y' = 3
    trans.append(mgr.Implies(fpcs[7], mgr.Equals(x_y, ints[3])))
    # fpc = 8 -> same_y
    trans.append(mgr.Implies(fpcs[8], same_y))
    # fpc = 9 -> same_y
    trans.append(mgr.Implies(fpcs[9], same_y))
    # fpc = 10 -> y' = 4
    trans.append(mgr.Implies(fpcs[10], mgr.Equals(x_y, ints[4])))
    # fpc = 11 -> y' = 5
    trans.append(mgr.Implies(fpcs[11], mgr.Equals(x_y, ints[5])))
    # fpc = 12 -> same_y
    trans.append(mgr.Implies(fpcs[12], same_y))
    # fpc = 13 -> y' = 6
    trans.append(mgr.Implies(fpcs[13], mgr.Equals(x_y, ints[6])))
    # fpc = 14 -> y' = 7
    trans.append(mgr.Implies(fpcs[14], mgr.Equals(x_y, ints[7])))
    # fpc = -1 -> same_y
    trans.append(mgr.Implies(fpcend, same_y))

    trans = mgr.And(*cfg, *trans)

    fairness = mgr.Not(mgr.Equals(pc, m_1))
    return symbols, init, trans, fairness


def hints(env: PysmtEnv) -> FrozenSet[Hint]:
    assert isinstance(env, PysmtEnv)

    mgr = env.formula_manager
    pc = mgr.Symbol("pc", types.INT)
    fpc = mgr.Symbol("fpc", types.INT)
    x = mgr.Symbol("x", types.INT)
    y = mgr.Symbol("y", types.INT)
    d = mgr.Symbol("d", types.INT)
    symbs = frozenset([pc, fpc, x, y, d])

    i_0 = mgr.Int(0)
    i_1 = mgr.Int(1)

    x_x = symb_to_next(mgr, x)
    stutter = mgr.Equals(x_x, x)
    l0 = Location(env, mgr.Equals(x, i_1), mgr.Equals(d, i_0), stutterT=stutter)
    l0.set_progress(0, mgr.Equals(x_x, mgr.Minus(x, d)))
    h_x = Hint("h_x", env, frozenset([x]), symbs)
    h_x.set_locs([l0])

    x_y = symb_to_next(mgr, y)
    stutter = mgr.Equals(x_y, y)
    l0 = Location(env, mgr.Equals(y, i_0), stutterT=stutter)
    l0.set_progress(0, mgr.Equals(x_y, i_0))
    h_y = Hint("h_y", env, frozenset([y]), symbs)
    h_y.set_locs([l0])

    x_d = symb_to_next(mgr, d)
    stutter = mgr.Equals(x_d, d)
    l0 = Location(env, mgr.Equals(d, i_1), stutterT=stutter)
    l0.set_progress(1, mgr.Equals(x_d, mgr.Minus(d, i_1)))
    l1 = Location(env, mgr.Equals(d, i_0), stutterT=stutter)
    l1.set_progress(1, mgr.Equals(x_d, d))
    h_d = Hint("h_d", env, frozenset([d]), symbs)
    h_d.set_locs([l0, l1])

    return frozenset([h_x, h_y, h_d])
