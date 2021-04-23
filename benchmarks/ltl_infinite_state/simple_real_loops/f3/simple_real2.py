from pysmt.environment import Environment as PysmtEnv
from pysmt.fnode import FNode
import pysmt.typing as types

from utils import symb_to_next


def transition_system(env: PysmtEnv) -> (frozenset, FNode, FNode, FNode):
    assert isinstance(env, PysmtEnv)
    mgr = env.formula_manager
    b = mgr.Symbol("b", types.BOOL)
    x = mgr.Symbol("x", types.REAL)
    x_x = symb_to_next(mgr, x)
    x_b = symb_to_next(mgr, b)
    r_0 = mgr.Real(0)
    r_1 = mgr.Real(1)
    r_m1 = mgr.Real(-1)
    init = mgr.GE(x, r_0)
    # b -> x' < -(x + 1) & !b'
    trans0 = mgr.Implies(b,
                         mgr.And(mgr.LT(x_x, mgr.Times(r_m1,
                                                       mgr.Plus(x, r_1))),
                                 mgr.Not(x_b)))
    # !b -> x' > -(x - 1) & b
    trans1 = mgr.Implies(mgr.Not(b),
                         mgr.And(mgr.GT(x_x, mgr.Times(r_m1,
                                                       mgr.Minus(x, r_1))),
                                 x_b))
    trans = mgr.And(trans0, trans1)
    fairness = mgr.GT(x, r_0)
    symbols = frozenset([b, x])
    return symbols, init, trans, fairness
