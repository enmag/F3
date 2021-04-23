from collections import Iterable
from mathsat import msat_term, msat_env
from mathsat import msat_make_constant, msat_declare_function
from mathsat import msat_get_integer_type, msat_get_rational_type
from mathsat import msat_make_and, msat_make_not, msat_make_or
from mathsat import msat_make_leq, msat_make_equal
from mathsat import msat_make_number, msat_make_plus
from ltl.ltl import TermMap, LTLEncoder
from utils import name_next


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


def check_ltl(menv: msat_env, enc: LTLEncoder) -> (Iterable, msat_term,
                                                   msat_term, msat_term):
    assert menv
    assert isinstance(menv, msat_env)
    assert enc
    assert isinstance(enc, LTLEncoder)
    real_type = msat_get_rational_type(menv)
    i = msat_declare_function(menv, "i", real_type)
    i = msat_make_constant(menv, i)
    r = msat_declare_function(menv, "r", real_type)
    r = msat_make_constant(menv, r)
    m_x_i = msat_declare_function(menv, "m_x_i", real_type)
    m_x_i = msat_make_constant(menv, m_x_i)

    x_m_x_i = msat_declare_function(menv, name_next("m_x_i"), real_type)
    x_m_x_i = msat_make_constant(menv, x_m_x_i)
    x_i = msat_declare_function(menv, name_next("i"), real_type)
    x_i = msat_make_constant(menv, x_i)
    x_r = msat_declare_function(menv, name_next("r"), real_type)
    x_r = msat_make_constant(menv, x_r)

    curr2next = {i: x_i, r: x_r, m_x_i: x_m_x_i}

    zero = msat_make_number(menv, "0")
    one = msat_make_number(menv, "1")
    l = msat_make_number(menv, "10")

    r_gt_0 = msat_make_gt(menv, r, zero)
    r_lt_l = msat_make_lt(menv, r, l)
    i_geq_0 = msat_make_geq(menv, i, zero)
    init = msat_make_and(menv, r_gt_0, r_lt_l)
    init = msat_make_and(menv, init, i_geq_0)
    # r' = r
    trans = msat_make_equal(menv, x_r, r)
    # i < l -> i' = i + 1
    i_lt_l = msat_make_lt(menv, i, l)
    x_i_eq_i_p_1 = msat_make_equal(menv, x_i,
                                   msat_make_plus(menv, i, one))
    trans = msat_make_and(menv, trans,
                          msat_make_impl(menv, i_lt_l, x_i_eq_i_p_1))
    # i >= l -> i' = 0
    i_geq_l = msat_make_geq(menv, i, l)
    x_i_eq_0 = msat_make_equal(menv, x_i, zero)
    trans = msat_make_and(menv, trans,
                          msat_make_impl(menv, i_geq_l, x_i_eq_0))
    # i' = m_x_i
    trans = msat_make_and(menv, trans,
                          msat_make_equal(menv, x_i, m_x_i))

    # (G F i' > i) -> ! G F r > i
    x_i_gt_i = msat_make_gt(menv, m_x_i, i)
    G_F_x_i_gt_i = enc.make_G(enc.make_F(x_i_gt_i))
    r_gt_i = msat_make_gt(menv, r, i)
    n_G_F_r_gt_i = msat_make_not(menv, enc.make_G(enc.make_F(r_gt_i)))
    ltl = msat_make_impl(menv, G_F_x_i_gt_i, n_G_F_r_gt_i)

    return TermMap(curr2next), init, trans, ltl
