from typing import Tuple, Iterable
from mathsat import msat_term, msat_env
from mathsat import msat_make_constant, msat_declare_function
from mathsat import msat_get_bool_type, msat_get_rational_type
from mathsat import msat_make_and, msat_make_not, msat_make_or
from mathsat import msat_make_leq, msat_make_equal
from mathsat import msat_make_number, msat_make_plus
from ltl.ltl import TermMap, LTLEncoder
from expr_utils import name2next


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
    real_type = msat_get_rational_type(menv)
    bool_type = msat_get_bool_type(menv)
    i = msat_declare_function(menv, "i", real_type)
    i = msat_make_constant(menv, i)
    r = msat_declare_function(menv, "r", real_type)
    r = msat_make_constant(menv, r)
    inc_i = msat_declare_function(menv, "inc_i", bool_type)
    inc_i = msat_make_constant(menv, inc_i)

    x_inc_i = msat_declare_function(menv, name2next("inc_i"), bool_type)
    x_inc_i = msat_make_constant(menv, x_inc_i)
    x_i = msat_declare_function(menv, name2next("i"), real_type)
    x_i = msat_make_constant(menv, x_i)
    x_r = msat_declare_function(menv, name2next("r"), real_type)
    x_r = msat_make_constant(menv, x_r)

    curr2next = {i: x_i, r: x_r, inc_i: x_inc_i}

    zero = msat_make_number(menv, "0")
    one = msat_make_number(menv, "1")
    l = msat_make_number(menv, "10")

    r_gt_0 = msat_make_gt(menv, r, zero)
    r_lt_l = msat_make_lt(menv, r, l)
    i_geq_0 = msat_make_geq(menv, i, zero)
    init = msat_make_and(menv, r_gt_0, r_lt_l)
    init = msat_make_and(menv, init,
                         msat_make_and(menv, i_geq_0,
                                       msat_make_not(menv, inc_i)))
    n_x_inc_i = msat_make_not(menv, x_inc_i)
    # r' = r
    trans = msat_make_equal(menv, x_r, r)
    # i < l -> ((inc_i' & i' = i + 1) | (!inc_i' & i' = i))
    i_lt_l = msat_make_lt(menv, i, l)
    x_i_eq_i_p_1 = msat_make_equal(menv, x_i,
                                   msat_make_plus(menv, i, one))
    x_i_eq_i = msat_make_equal(menv, x_i, i)
    x_i_eq_i_p_1_or_i = msat_make_or(
        menv,
        msat_make_and(menv, x_inc_i, x_i_eq_i_p_1),
        msat_make_and(menv, n_x_inc_i, x_i_eq_i))
    trans = msat_make_and(menv, trans,
                          msat_make_impl(menv, i_lt_l, x_i_eq_i_p_1_or_i))
    # i >= l -> (!inc_i' & i' = 0)
    i_geq_l = msat_make_geq(menv, i, l)
    x_i_eq_0 = msat_make_equal(menv, x_i, zero)
    trans = msat_make_and(
        menv, trans,
        msat_make_impl(menv, i_geq_l,
                       msat_make_and(menv, n_x_inc_i, x_i_eq_0)))

    # (G F inc_i) -> ! G F r > i
    GF_inc_i = enc.make_G(enc.make_F(inc_i))
    r_gt_i = msat_make_gt(menv, r, i)
    n_GF_r_gt_i = msat_make_not(menv, enc.make_G(enc.make_F(r_gt_i)))
    ltl = msat_make_impl(menv, GF_inc_i, n_GF_r_gt_i)

    return TermMap(curr2next), init, trans, ltl
