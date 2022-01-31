from typing import Tuple, FrozenSet
from pysmt.environment import Environment as PysmtEnv
from pysmt.fnode import FNode
import pysmt.typing as types

from expr_utils import symb2next


def transition_system(env: PysmtEnv) -> Tuple[FrozenSet[FNode], FNode,
                                              FNode, FNode]:
    assert isinstance(env, PysmtEnv)
    mgr = env.formula_manager
    b = mgr.Symbol("b", types.BOOL)
    x = mgr.Symbol("x", types.REAL)
    x_x = symb2next(env, x)
    r_0 = mgr.Real(0)
    r_1 = mgr.Real(1)
    r_m1 = mgr.Real(-1)
    init = mgr.GE(x, r_0)
    # b -> x' < - (x + 1)
    trans0 = mgr.Implies(b, mgr.LT(x_x, mgr.Times(r_m1, mgr.Plus(x, r_1))))
    # !b -> x' < - (x + 1)
    trans1 = mgr.Implies(mgr.Not(b),
                         mgr.GT(x_x, mgr.Times(r_m1, mgr.Minus(x, r_1))))
    trans = mgr.And(trans0, trans1)
    fairness = mgr.GT(x, r_0)
    symbols = frozenset([b, x])
    return symbols, init, trans, fairness
