from typing import Tuple, FrozenSet
from pysmt.environment import Environment as PysmtEnv
from pysmt.fnode import FNode
import pysmt.typing as types

from expr_utils import symb2next


def transition_system(env: PysmtEnv) -> Tuple[FrozenSet[FNode], FNode,
                                              FNode, FNode]:
    assert isinstance(env, PysmtEnv)
    mgr = env.formula_manager
    x = mgr.Symbol("x", types.INT)
    x_x = symb2next(env, x)
    i_0 = mgr.Int(0)
    i_1 = mgr.Int(1)
    i_m1 = mgr.Int(-1)
    init = mgr.GE(x, i_0)
    # x > 0 -> x' < - (x + 1)
    trans0 = mgr.Implies(mgr.GT(x, i_0),
                         mgr.LT(x_x, mgr.Times(i_m1, mgr.Plus(x, i_1))))
    # x <= 0 -> x' > - (x - 1)
    trans1 = mgr.Implies(mgr.LE(x, i_0),
                         mgr.GT(x_x, mgr.Times(i_m1, mgr.Minus(x, i_1))))
    trans = mgr.And(trans0, trans1)
    fairness = init
    symbols = frozenset([x])
    return symbols, init, trans, fairness
