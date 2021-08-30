from typing import Tuple, FrozenSet

from pysmt.environment import Environment as PysmtEnv
from pysmt.fnode import FNode
import pysmt.typing as types

from mathsat import msat_term, msat_env
from mathsat import msat_make_constant, msat_declare_function
from mathsat import msat_get_integer_type, msat_get_rational_type
from mathsat import msat_make_and, msat_make_not, msat_make_or
from mathsat import msat_make_leq, msat_make_equal
from mathsat import msat_make_number, msat_make_plus

from utils import name_next, symb_to_next
from hint import Hint, Location
from rankfun import RankFun


def transition_system(env: PysmtEnv) -> Tuple[FrozenSet[FNode], FNode,
                                              FNode, FNode]:
    assert isinstance(env, PysmtEnv)
    mgr = env.formula_manager
    i = mgr.Symbol("i", types.REAL)
    r = mgr.Symbol("r", types.REAL)
    l = mgr.Symbol("l", types.REAL)
    inc_i = mgr.Symbol("inc_i", types.BOOL)
    symbs = frozenset([i, r, l, inc_i])

    x_i = symb_to_next(mgr, i)
    x_r = symb_to_next(mgr, r)
    x_l = symb_to_next(mgr, l)

    n0 = mgr.Real(0)
    n1 = mgr.Real(1)

    init = mgr.And(mgr.GT(r, n0), mgr.LT(r, l), mgr.GE(i, n0))
    cond = mgr.LT(i, l)
    trans = mgr.And(
        # r' = r
        mgr.Equals(x_r, r),
        # i < l -> inc_i & i' >= i + 1 & l' = l
        mgr.Implies(cond,
                    mgr.And(inc_i,
                            mgr.GE(x_i, mgr.Plus(i, n1)),
                            mgr.Equals(x_l, l))),
        # i >= l -> ! inc_i & i' = 0 & l' >= l + 1
        mgr.Implies(mgr.Not(cond),
                    mgr.And(mgr.Not(inc_i),
                            mgr.Equals(x_i, n0),
                            mgr.GE(x_l, mgr.Plus(l, n1)))))

    return symbs, init, trans, inc_i


def hints(env: PysmtEnv) -> FrozenSet[Hint]:
    assert isinstance(env, PysmtEnv)

    mgr = env.formula_manager
    i = mgr.Symbol("i", types.REAL)
    r = mgr.Symbol("r", types.REAL)
    inc_i = mgr.Symbol("inc_i", types.BOOL)
    l = mgr.Symbol("l", types.REAL)
    symbs = frozenset([i, r, l, inc_i])
    x_i = symb_to_next(mgr, i)
    x_r = symb_to_next(mgr, r)
    x_l = symb_to_next(mgr, l)

    n0 = mgr.Real(0)
    n1 = mgr.Real(1)
    n2 = mgr.Real(2)

    delta = n1
    rankT = mgr.And(mgr.Equals(x_i, mgr.Plus(i, n1)),
                    mgr.Equals(x_r, r),
                    mgr.Equals(x_l, l))
    rf0 = mgr.Minus(r, i)
    rf0 = RankFun(env, rf0, delta, frozenset([i, r]))
    loc0 = Location(env, mgr.And(mgr.LT(i, mgr.Plus(r, n1)),
                                 mgr.LE(mgr.Plus(r, n2), l)),
                    rankT=rankT, rf=rf0)
    loc0.set_progress(1, rankT)
    rf1 = mgr.Minus(l, i)
    rf1 = RankFun(env, rf1, delta, frozenset([i, r]))
    loc1 = Location(env, mgr.And(mgr.LE(i, l), mgr.LT(r, i),
                                 mgr.LE(mgr.Plus(r, n2), l)),
                    rankT=rankT, rf=rf1)
    loc1.set_progress(0, mgr.And(mgr.Equals(x_i, n0),
                                 mgr.Equals(x_r, r),
                                 mgr.Equals(x_l, mgr.Plus(l, n1))))
    h_irl = Hint("h_irl", env, frozenset([i, r, l]), symbs)
    h_irl.set_locs([loc0, loc1])

    return frozenset([h_irl])
