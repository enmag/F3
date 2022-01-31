import pysmt.typing as types
from typing import Tuple, FrozenSet
from pysmt.environment import Environment as PysmtEnv
from pysmt.fnode import FNode
from expr_utils import symb2next


def transition_system(env: PysmtEnv) -> Tuple[FrozenSet[FNode], FNode, FNode, FNode]:
    assert isinstance(env, PysmtEnv)
    mgr = env.formula_manager
    pc = mgr.Symbol("pc", types.INT)
    i = mgr.Symbol("i", types.REAL)
    j = mgr.Symbol("j", types.REAL)
    x_pc = symb2next(env, pc)
    x_i = symb2next(env, i)
    x_j = symb2next(env, j)
    symbols = frozenset([pc, i, j])

    n_locs = 4
    int_bound = n_locs
    pcs = []
    x_pcs = []
    ints = [mgr.Int(i) for i in range(int_bound)]

    for l in range(n_locs):
        n = ints[l]
        pcs.append(mgr.Equals(pc, n))
        x_pcs.append(mgr.Equals(x_pc, n))

    r_0 = mgr.Real(0)
    r_1 = mgr.Real(1)
    r_3 = mgr.Real(3)

    # initial condition.
    init = mgr.Equals(pc, ints[0])
    # transition relation.
    trans = mgr.And(
        mgr.Implies(
            # pc = 0 & i < 0 -> pc' = 3,
            mgr.And(mgr.Equals(pc, ints[0]), mgr.LT(i, r_0)),
            mgr.Equals(x_pc, ints[3])),
        # pc = 0 & i >= 0 -> pc' = 1
        mgr.Implies(
            mgr.And(mgr.Equals(pc, ints[0]), mgr.GE(i, r_0)),
            mgr.And(mgr.Equals(x_pc, ints[1]), mgr.Equals(x_i, i),
                    mgr.Equals(x_j, j))),
        # pc = 1 -> pc' = 2 & i' = i + j
        mgr.Implies(
            mgr.Equals(pc, ints[1]),
            mgr.And(mgr.Equals(x_pc, ints[2]), mgr.Equals(x_j, j),
                    mgr.Equals(x_i, mgr.Plus(i, j)))),
        # pc = 2 -> pc' = 0 & j' = j^3/3 + 1
        mgr.Implies(
            mgr.Equals(pc, ints[2]),
            mgr.And(
                mgr.Equals(x_pc, ints[0]), mgr.Equals(x_i, i),
                mgr.Equals(x_j, mgr.Plus(mgr.Div(mgr.Times(j, j, j), r_3),
                                         r_1)))),
        # pc = 3 -> pc' = 3
        mgr.Implies(mgr.Equals(pc, ints[3]), mgr.Equals(x_pc, ints[3])))
    # fairness condition.
    fairness = mgr.Not(mgr.Equals(pc, ints[3]))

    return symbols, init, trans, fairness
