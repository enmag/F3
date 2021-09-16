from typing import Tuple, FrozenSet
from collections import Iterable

from mathsat import msat_term, msat_env
from mathsat import msat_make_constant, msat_declare_function
from mathsat import msat_get_integer_type, msat_get_rational_type,     msat_get_bool_type
from mathsat import msat_make_and, msat_make_not, msat_make_or
from mathsat import msat_make_leq, msat_make_equal
from mathsat import msat_make_number, msat_make_plus

from pysmt.environment import Environment as PysmtEnv
import pysmt.typing as types

from ltl.ltl import TermMap, LTLEncoder
from utils import name_next, symb_to_next
from hint import Hint, Location


def msat_make_lt(menv: msat_env, arg0: msat_term, arg1: msat_term):
    geq = msat_make_geq(menv, arg0, arg1)
    return msat_make_not(menv, geq)


def msat_make_geq(menv: msat_env, arg0: msat_term, arg1: msat_term):
    return msat_make_leq(menv, arg1, arg0)


def msat_make_gt(menv: msat_env, arg0: msat_term, arg1: msat_term):
    leq = msat_make_leq(menv, arg0, arg1)
    return msat_make_not(menv, leq)


def msat_make_impl(menv: msat_env, arg0: msat_term, arg1: msat_term):
    n_arg0 = msat_make_not(menv, arg0)
    return msat_make_or(menv, n_arg0, arg1)


def check_ltl(menv: msat_env, enc: LTLEncoder) -> Tuple[Iterable, msat_term,
                                                        msat_term, msat_term]:
    assert menv
    assert isinstance(menv, msat_env)
    assert enc
    assert isinstance(enc, LTLEncoder)
    bool_type = msat_get_bool_type(menv)
    real_type = msat_get_rational_type(menv)
    i = msat_declare_function(menv, "i", real_type)
    i = msat_make_constant(menv, i)
    r = msat_declare_function(menv, "r", real_type)
    r = msat_make_constant(menv, r)
    l = msat_declare_function(menv, "l", real_type)
    l = msat_make_constant(menv, l)
    inc_i = msat_declare_function(menv, "inc_i", bool_type)
    inc_i = msat_make_constant(menv, inc_i)

    x_i = msat_declare_function(menv, name_next("i"), real_type)
    x_i = msat_make_constant(menv, x_i)
    x_r = msat_declare_function(menv, name_next("r"), real_type)
    x_r = msat_make_constant(menv, x_r)
    x_l = msat_declare_function(menv, name_next("l"), real_type)
    x_l = msat_make_constant(menv, x_l)
    x_inc_i = msat_declare_function(menv, name_next("inc_i"), bool_type)
    x_inc_i = msat_make_constant(menv, x_inc_i)

    curr2next = {i: x_i, r: x_r, l: x_l, inc_i: x_inc_i}

    zero = msat_make_number(menv, "0")
    one = msat_make_number(menv, "1")

    r_gt_0 = msat_make_gt(menv, r, zero)
    r_lt_l = msat_make_lt(menv, r, l)
    i_geq_0 = msat_make_geq(menv, i, zero)
    init = msat_make_and(menv, r_gt_0, r_lt_l)
    init = msat_make_and(menv, init,
                         msat_make_and(menv, i_geq_0,
                                       msat_make_not(menv, inc_i)))
    init = msat_make_and(menv, init, msat_make_gt(menv, l, zero))

    # r' = r
    trans = msat_make_equal(menv, x_r, r)
    # i < l -> ((inc_i' & i' = i + 1) | (!inc_i' & i' = i)) & l' = l
    i_lt_l = msat_make_lt(menv, i, l)
    x_i_eq_i_p_1 = msat_make_and(menv, x_inc_i,
                                 msat_make_equal(menv, x_i,
                                                 msat_make_plus(menv, i, one)))
    x_i_eq_i = msat_make_and(menv, msat_make_not(menv, x_inc_i),
                             msat_make_equal(menv, x_i, i))
    x_i_eq_i_p_1_or_i = msat_make_or(menv, x_i_eq_i_p_1, x_i_eq_i)
    x_l_eq_l = msat_make_equal(menv, x_l, l)
    x_i_eq_i_p_1_or_i_and_x_l_eq_l = msat_make_and(menv, x_i_eq_i_p_1_or_i,
                                                   x_l_eq_l)
    trans = msat_make_and(menv, trans,
                          msat_make_impl(menv, i_lt_l,
                                         x_i_eq_i_p_1_or_i_and_x_l_eq_l))
    # i >= l -> i' = 0 & l' = l + 1 & !inc_i'
    i_geq_l = msat_make_geq(menv, i, l)
    x_i_eq_0 = msat_make_equal(menv, x_i, zero)
    x_l_eq_l_p_1 = msat_make_equal(menv, x_l, msat_make_plus(menv, l, one))
    x_i_eq_0_and_x_l_eq_l_p_1 = msat_make_and(menv,
                                              msat_make_and(menv, x_i_eq_0,
                                                            x_l_eq_l_p_1),
                                              msat_make_not(menv, x_inc_i))
    trans = msat_make_and(menv, trans,
                          msat_make_impl(menv, i_geq_l,
                                         x_i_eq_0_and_x_l_eq_l_p_1))

    # (G F inc_i) -> ! G F r > i
    G_F_x_i_gt_i = enc.make_G(enc.make_F(inc_i))
    r_gt_i = msat_make_gt(menv, r, i)
    n_G_F_r_gt_i = msat_make_not(menv, enc.make_G(enc.make_F(r_gt_i)))
    ltl = msat_make_impl(menv, G_F_x_i_gt_i, n_G_F_r_gt_i)

    return TermMap(curr2next), init, trans, ltl


def hints(env: PysmtEnv) -> FrozenSet[Hint]:
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
    x_inc_i = symb_to_next(mgr, inc_i)

    res = []

    n0 = mgr.Real(0)
    n1 = mgr.Real(1)

    loc = Location(env, mgr.LE(r, n0))
    loc.set_progress(0, mgr.Equals(x_r, mgr.Minus(r, n1)))
    h_r = Hint("h_r1", env, frozenset([r]), symbs)
    h_r.set_locs([loc])
    res.append(h_r)


    loc0 = Location(env, mgr.Not(inc_i))
    loc0.set_progress(1, x_inc_i)
    loc1 = Location(env, inc_i, stutterT=x_inc_i)
    loc1.set_progress(0, mgr.Not(x_inc_i))
    h_inc = Hint("h_inc3", env, frozenset([inc_i]), symbs)
    h_inc.set_locs([loc0, loc1])
    res.append(h_inc)


    loc0 = Location(env, mgr.GE(i, n0))
    loc0.set_progress(1, mgr.Equals(x_i, mgr.Plus(i, n1)))
    loc1 = Location(env, mgr.GE(i, n0))
    loc1.set_progress(2, mgr.Equals(x_i, i))
    loc2 = Location(env, mgr.GE(i, n0))
    loc2.set_progress(0, mgr.Equals(x_i, i))
    h_i = Hint("h_i4", env, frozenset([i]), symbs)
    h_i.set_locs([loc0, loc1, loc2])
    res.append(h_i)


    loc = Location(env, mgr.GE(l, n0))
    loc.set_progress(0, mgr.Equals(x_l, mgr.Plus(l, n1)))
    h_l = Hint("h_l0", env, frozenset([l]), symbs)
    h_l.set_locs([loc])
    res.append(h_l)


    loc = Location(env, mgr.Not(inc_i))
    loc.set_progress(0, mgr.Not(x_inc_i))
    h_inc = Hint("h_inc1", env, frozenset([inc_i]), symbs)
    h_inc.set_locs([loc])
    res.append(h_inc)


    loc0 = Location(env, mgr.GE(r, n0))
    loc0.set_progress(1, mgr.Equals(x_r, r))
    loc1 = Location(env, mgr.GE(r, n0))
    loc1.set_progress(2, mgr.Equals(x_r, mgr.Plus(r, n1)))
    loc2 = Location(env, mgr.GE(r, n0))
    loc2.set_progress(0, mgr.Equals(x_r, r))
    h_r = Hint("h_r4", env, frozenset([r]), symbs)
    h_r.set_locs([loc0, loc1, loc2])
    res.append(h_r)


    loc0 = Location(env, mgr.GE(l, n0))
    loc0.set_progress(1, mgr.Equals(x_l, mgr.Plus(l, n1)))
    loc1 = Location(env, mgr.GE(l, n0))
    loc1.set_progress(0, mgr.Equals(x_l, l))
    h_l = Hint("h_l2", env, frozenset([l]), symbs)
    h_l.set_locs([loc0, loc1])
    res.append(h_l)


    loc0 = Location(env, mgr.Not(inc_i))
    loc0.set_progress(1, x_inc_i)
    loc1 = Location(env, inc_i, stutterT=x_inc_i)
    loc1.set_progress(2, mgr.Not(x_inc_i))
    loc2 = Location(env, mgr.Not(inc_i))
    loc2.set_progress(0, mgr.Not(x_inc_i))
    h_inc = Hint("h_inc4", env, frozenset([inc_i]), symbs)
    h_inc.set_locs([loc0, loc1, loc2])
    res.append(h_inc)


    loc0 = Location(env, mgr.GE(r, n0))
    loc0.set_progress(1, mgr.Equals(x_r, r))
    loc1 = Location(env, mgr.GE(r, n0))
    loc1.set_progress(0, mgr.Equals(x_r, mgr.Plus(r, n1)))
    h_r = Hint("h_r2", env, frozenset([r]), symbs)
    h_r.set_locs([loc0, loc1])
    res.append(h_r)


    loc = Location(env, mgr.GE(r, n0))
    loc.set_progress(0, mgr.Equals(x_r, mgr.Plus(r, n1)))
    h_r = Hint("h_r0", env, frozenset([r]), symbs)
    h_r.set_locs([loc])
    res.append(h_r)


    loc0 = Location(env, mgr.GE(i, n0), mgr.GE(l, n0),
                    stutterT=mgr.Equals(x_i, mgr.Plus(i, l)))
    loc0.set_progress(1, mgr.Equals(x_i, mgr.Plus(i, n1)))
    loc1 = Location(env, mgr.GE(i, n0))
    loc1.set_progress(0, mgr.Equals(x_i, i))
    h_i = Hint("h_i3", env, frozenset([i]), symbs)
    h_i.set_locs([loc0, loc1])
    res.append(h_i)


    stutter = mgr.Equals(x_i, i)
    loc = Location(env, mgr.GE(i, n0), stutterT=stutter)
    loc.set_progress(0, mgr.Equals(x_i, mgr.Plus(i, n1)))
    h_i = Hint("h_i0", env, frozenset([i]), symbs)
    h_i.set_locs([loc])
    res.append(h_i)

    return frozenset(res)
