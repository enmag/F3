from pysmt.environment import Environment as PysmtEnv
from pysmt.fnode import FNode
import pysmt.typing as types

from utils import symb_to_next


def transition_system(env: PysmtEnv) -> (frozenset, FNode, FNode, FNode):
    assert isinstance(env, PysmtEnv)
    mgr = env.formula_manager
    x = mgr.Symbol("x", types.REAL)
    x_x = symb_to_next(mgr, x)
    r_0 = mgr.Real(0)
    r_1 = mgr.Real(1)
    r_m1 = mgr.Real(-1)
    init = mgr.GE(x, r_0)
    # x > 0 -> x' < - (x + 1)
    trans0 = mgr.Implies(mgr.GT(x, r_0),
                         mgr.LT(x_x, mgr.Times(r_m1, mgr.Plus(x, r_1))))
    # x <= 0 -> x' > - (x - 1)
    trans1 = mgr.Implies(mgr.LE(x, r_0),
                         mgr.GT(x_x, mgr.Times(r_m1, mgr.Minus(x, r_1))))
    trans = mgr.And(trans0, trans1)
    fairness = init
    symbols = frozenset([x])
    return symbols, init, trans, fairness
