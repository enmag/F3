from pysmt.environment import Environment as PysmtEnv
from pysmt.fnode import FNode
import pysmt.typing as types

from utils import symb_to_next


def transition_system(env: PysmtEnv) -> (frozenset, FNode, FNode, FNode):
    """Infinite fair path: b & x > 0; !b & x < 0"""
    assert isinstance(env, PysmtEnv)
    mgr = env.formula_manager
    b = mgr.Symbol("b", types.BOOL)
    x = mgr.Symbol("x", types.INT)
    x_x = symb_to_next(mgr, x)
    x_b = symb_to_next(mgr, b)
    i_0 = mgr.Int(0)
    i_1 = mgr.Int(1)
    i_m1 = mgr.Int(-1)
    init = mgr.GE(x, i_0)
    # b -> x' < - (x + 1) & !b'
    trans0 = mgr.Implies(b,
                         mgr.And(mgr.LT(x_x, mgr.Times(i_m1,
                                                       mgr.Plus(x, i_1))),
                                 mgr.Not(x_b)))
    # !b -> x' > - (x - 1) & b'
    trans1 = mgr.Implies(mgr.Not(b),
                         mgr.And(mgr.GT(x_x, mgr.Times(i_m1,
                                                       mgr.Minus(x, i_1))),
                                 x_b))
    trans = mgr.And(trans0, trans1)
    fairness = mgr.GT(x, i_0)
    symbols = frozenset([b, x])
    return symbols, init, trans, fairness
