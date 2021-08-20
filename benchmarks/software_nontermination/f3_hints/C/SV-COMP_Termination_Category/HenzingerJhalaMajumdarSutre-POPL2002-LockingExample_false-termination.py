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
    lock = mgr.Symbol("LOCK", types.INT)
    x_lock = symb_to_next(mgr, lock)
    got_lock = mgr.Symbol("got_lock", types.INT)
    x_got_lock = symb_to_next(mgr, got_lock)
    old = mgr.Symbol("old", types.INT)
    x_old = symb_to_next(mgr, old)
    new = mgr.Symbol("new", types.INT)
    x_new = symb_to_next(mgr, new)

    symbols = frozenset([pc, lock, got_lock, old, new])

    m_1 = mgr.Int(-1)

    n_locs = 17
    max_int = n_locs
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

    init = pcs[0]
    cfg = []
    # pc = 0 -> pc' = 1 | pc' = 9
    cfg.append(mgr.Implies(pcs[0], mgr.Or(x_pcs[1], x_pcs[9])))
    # pc = 1 -> pc' = 2
    cfg.append(mgr.Implies(pcs[1], x_pcs[2]))
    # pc = 2 -> pc' = 3
    cfg.append(mgr.Implies(pcs[2], x_pcs[3]))
    # pc = 3 -> pc' = 4 | pc' = 6
    cfg.append(mgr.Implies(pcs[3], mgr.Or(x_pcs[4], x_pcs[6])))
    # pc = 4 -> pc' = 5
    cfg.append(mgr.Implies(pcs[4], x_pcs[5]))
    # pc = 5 -> pc' = 6
    cfg.append(mgr.Implies(pcs[5], x_pcs[6]))
    # pc = 6 & got_lock > 0 -> pc' = 7
    cond = mgr.GT(got_lock, ints[0])
    cfg.append(mgr.Implies(mgr.And(pcs[6], cond), x_pcs[7]))
    # pc = 6 & !(got_lock > 0) -> pc' = 8
    cfg.append(mgr.Implies(mgr.And(pcs[6], mgr.Not(cond)), x_pcs[8]))
    # pc = 8 -> pc' = 1 | pc' = 9
    cfg.append(mgr.Implies(pcs[8], mgr.Or(x_pcs[1], x_pcs[9])))
    # pc = 9 -> pc' = 10
    cfg.append(mgr.Implies(pcs[9], x_pcs[10]))
    # pc = 10 -> pc' = 11
    cfg.append(mgr.Implies(pcs[10], x_pcs[11]))
    # pc = 11 -> pc' = 12
    cfg.append(mgr.Implies(pcs[11], x_pcs[12]))
    # pc = 12 -> pc' = 13 | pc' = 15
    cfg.append(mgr.Implies(pcs[12], mgr.Or(x_pcs[13], x_pcs[15])))
    # pc = 13 -> pc' = 14
    cfg.append(mgr.Implies(pcs[13], x_pcs[14]))
    # pc = 14 -> pc' = 15
    cfg.append(mgr.Implies(pcs[14], x_pcs[15]))
    # pc = 15 & new != old -> pc' = 9
    cond = mgr.Not(mgr.Equals(new, old))
    cfg.append(mgr.Implies(mgr.And(pcs[15], cond), x_pcs[9]))
    # pc = 15 & !(new != old) -> pc' = 16
    cfg.append(mgr.Implies(mgr.And(pcs[15], mgr.Not(cond)), x_pcs[16]))
    # pc = 16 -> pc' = -1
    cfg.append(mgr.Implies(pcs[16], x_pcend))
    # pc = -1 -> pc' = -1
    cfg.append(mgr.Implies(pcend, x_pcend))

    trans = []
    same_lock = mgr.Equals(x_lock, lock)
    same_got_lock = mgr.Equals(x_got_lock, got_lock)
    same_old = mgr.Equals(x_old, old)
    same_new = mgr.Equals(x_new, new)
    same = mgr.And(same_lock, same_got_lock, same_old, same_new)
    # pc = 0 -> same
    trans.append(mgr.Implies(pcs[0], same))
    # pc = 1 -> same
    trans.append(mgr.Implies(pcs[1], same))
    # pc = 2 -> same_lock & got_lock' = 0 & same_old & same_new
    trans.append(mgr.Implies(pcs[2],
                             mgr.And(same_lock, mgr.Equals(x_got_lock,
                                                           ints[0]),
                                     same_old, same_new)))
    # pc = 3 -> same
    trans.append(mgr.Implies(pcs[3], same))
    # pc = 4 -> lock' = 1 & same_got_lock & same_old & same_new
    trans.append(mgr.Implies(pcs[4],
                             mgr.And(mgr.Equals(x_lock, ints[1]),
                                     same_got_lock, same_old, same_new)))
    # pc = 5 -> same_lock & got_lock' = got_lock + 1 & same_old & same_new
    trans.append(mgr.Implies(pcs[5], mgr.And(same_lock,
                                             mgr.Equals(x_got_lock,
                                                        mgr.Plus(got_lock,
                                                                 ints[1])),
                                             same_old, same_new)))
    # pc = 6 -> same
    trans.append(mgr.Implies(pcs[6], same))
    # pc = 7 -> lock' = 0 & same_got_lock & same_old & same_new
    trans.append(mgr.Implies(pcs[7],
                             mgr.And(mgr.Equals(x_lock, ints[0]),
                                     same_got_lock, same_old, same_new)))
    # pc = 8 -> same
    trans.append(mgr.Implies(pcs[8], same))
    # pc = 9 -> same
    trans.append(mgr.Implies(pcs[9], same))
    # pc = 10 -> lock' = 1 & same_got_lock & same_old & same_new
    trans.append(mgr.Implies(pcs[10],
                             mgr.And(mgr.Equals(x_lock, ints[1]),
                                     same_got_lock, same_old, same_new)))
    # pc = 11 -> same_lock & same_old_lock & old' = new & same_new
    trans.append(mgr.Implies(pcs[11],
                             mgr.And(same_lock, same_got_lock,
                                     mgr.Equals(x_old, new), same_new)))
    # pc = 12 -> same
    trans.append(mgr.Implies(pcs[12], same))
    # pc = 13 -> lock' = 0 & same_got_lock & same_old & same_new
    trans.append(mgr.Implies(pcs[13],
                             mgr.And(mgr.Equals(x_lock, ints[0]),
                                     same_got_lock, same_old, same_new)))
    # pc = 14 -> same_lock & same_got_lock & same_old & new' = new + 1
    trans.append(mgr.Implies(pcs[14],
                             mgr.And(same_lock, same_got_lock, same_old,
                                     mgr.Equals(x_new,
                                                mgr.Plus(new, ints[1])))))
    # pc = 15 -> same
    trans.append(mgr.Implies(pcs[15], same))
    # pc = 16 -> lock' = 0 & same_got_lock & same_old & same_new
    trans.append(mgr.Implies(pcs[16],
                             mgr.And(mgr.Equals(x_lock, ints[0]),
                                     same_got_lock, same_old, same_new)))
    # pc = end -> same
    trans.append(mgr.Implies(pcend, same))

    trans = mgr.And(*cfg, *trans)

    fairness = mgr.Not(mgr.Equals(pc, m_1))
    return symbols, init, trans, fairness


def hints(env: PysmtEnv) -> FrozenSet[Hint]:
    assert isinstance(env, PysmtEnv)

    mgr = env.formula_manager
    pc = mgr.Symbol("pc", types.INT)
    lock = mgr.Symbol("LOCK", types.INT)
    got_lock = mgr.Symbol("got_lock", types.INT)
    old = mgr.Symbol("old", types.INT)
    new = mgr.Symbol("new", types.INT)
    symbs = frozenset([pc, lock, got_lock, old, new])

    i_0 = mgr.Int(0)

    x_lock = symb_to_next(mgr, lock)
    stutter = mgr.Equals(x_lock, lock)
    l0 = Location(env, mgr.Equals(lock, i_0), stutterT=stutter)
    l0.set_progress(0, eq_0=mgr.Equals(x_lock, i_0))
    h_lock = Hint("h_lock", env, frozenset([lock]), symbs)
    h_lock.set_locs([l0])

    x_got_lock = symb_to_next(mgr, got_lock)
    stutter = mgr.Equals(x_got_lock, got_lock)
    l0 = Location(env, mgr.Equals(got_lock, i_0), stutterT=stutter)
    l0.set_progress(0, eq_0=mgr.Equals(x_got_lock, i_0))
    h_got_lock = Hint("h_got_lock", env, frozenset([got_lock]), symbs)
    h_got_lock.set_locs([l0])

    x_old = symb_to_next(mgr, old)
    stutter = mgr.Equals(x_old, old)
    l0 = Location(env, mgr.Equals(old, i_0), stutterT=stutter)
    l0.set_progress(0, eq_0=mgr.Equals(x_old, i_0))
    h_old = Hint("h_old", env, frozenset([old]), symbs)
    h_old.set_locs([l0])

    x_new = symb_to_next(mgr, new)
    stutter = mgr.Equals(x_new, new)
    l0 = Location(env, mgr.Equals(new, i_0), stutterT=stutter)
    l0.set_progress(0, eq_0=mgr.Equals(x_new, i_0))
    h_new = Hint("h_new", env, frozenset([new]), symbs)
    h_new.set_locs([l0])

    return frozenset([h_lock, h_got_lock, h_old, h_new])
