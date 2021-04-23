from mathsat import msat_term, msat_env
from mathsat import msat_make_constant, msat_declare_function
from mathsat import msat_get_rational_type, msat_get_integer_type, \
    msat_get_bool_type
from mathsat import msat_make_and, msat_make_not, msat_make_or, msat_make_iff
from mathsat import msat_make_leq, msat_make_equal, msat_make_true
from mathsat import msat_make_number, msat_make_plus, msat_make_times, \
    msat_make_divide

from ltl.ltl import TermMap, LTLEncoder
from utils import name_next


delta_name = "delta"


def decl_consts(menv: msat_env, name: str, c_type):
    assert not name.startswith("_"), name
    s = msat_declare_function(menv, name, c_type)
    s = msat_make_constant(menv, s)
    x_s = msat_declare_function(menv, name_next(name), c_type)
    x_s = msat_make_constant(menv, x_s)
    return s, x_s


def msat_make_minus(menv: msat_env, arg0: msat_term, arg1: msat_term):
    m_one = msat_make_number(menv, "-1")
    arg1 = msat_make_times(menv, arg1, m_one)
    return msat_make_plus(menv, arg0, arg1)


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


def diverging_symbs(menv: msat_env) -> frozenset:
    real_type = msat_get_rational_type(menv)
    delta = msat_declare_function(menv, delta_name, real_type)
    delta = msat_make_constant(menv, delta)
    return frozenset([delta])

def check_ltl(menv: msat_env, enc: LTLEncoder):
    assert menv
    assert isinstance(menv, msat_env)
    assert enc
    assert isinstance(enc, LTLEncoder)

    bool_type = msat_get_bool_type(menv)
    int_type = msat_get_integer_type(menv)
    real_type = msat_get_rational_type(menv)
    h, x_h = decl_consts(menv, "h", real_type)
    v, x_v = decl_consts(menv, "v", real_type)
    d, x_d = decl_consts(menv, delta_name, real_type)
    c, x_c = decl_consts(menv, "counter", int_type)
    stop, x_stop = decl_consts(menv, "stop", bool_type)

    curr2next = {h: x_h, v: x_v, d: x_d, c: x_c, stop: x_stop}

    g = msat_make_number(menv, "9.81")
    m_1 = msat_make_number(menv, "-1")
    _0 = msat_make_number(menv, "0")
    half = msat_make_number(menv, "0.5")
    _1 = msat_make_number(menv, "1")
    _2 = msat_make_number(menv, "2")

    # initial location
    init = msat_make_and(menv,
                         msat_make_and(menv,
                                       msat_make_equal(menv, c, _1),
                                       msat_make_equal(menv, h, _0)),
                         msat_make_equal(menv, v,
                                         msat_make_divide(menv, g, _2)))
    # transition relation
    # c' = c + 1 if h = 0 & v < 0 else c
    cond = msat_make_and(menv,
                         msat_make_equal(menv, h, _0),
                         msat_make_lt(menv, v, _0))
    xc_eq_c_p_1 = msat_make_equal(menv, x_c,
                                  msat_make_plus(menv, c, _1))
    xc_eq_c = msat_make_equal(menv, x_c, c)
    trans = msat_make_and(menv,
                          msat_make_impl(menv, cond, xc_eq_c_p_1),
                          msat_make_impl(menv,
                                         msat_make_not(menv, cond),
                                         xc_eq_c))
    # h' = 0 if h = 0 & (stop | v <= 0) else h + vd - gdd/2
    vd = msat_make_times(menv, v, d)
    dd = msat_make_times(menv, d, d)
    gdd = msat_make_times(menv, g, dd)
    m_half_gdd = msat_make_times(menv, m_1,
                                 msat_make_times(menv, half, gdd))

    cond = msat_make_and(menv,
                         msat_make_equal(menv, h, _0),
                         msat_make_or(menv, stop,
                                      msat_make_leq(menv, v, _0)))
    xh_eq_h_p_vd_gdd = msat_make_plus(menv, h,
                                      msat_make_plus(menv, vd, m_half_gdd))
    xh_eq_h_p_vd_gdd = msat_make_equal(menv, x_h, xh_eq_h_p_vd_gdd)
    xh_eq_0 = msat_make_equal(menv, x_h, _0)
    curr = msat_make_and(menv,
                         msat_make_impl(menv, cond, xh_eq_0),
                         msat_make_impl(menv, msat_make_not(menv, cond),
                                        xh_eq_h_p_vd_gdd))
    trans = msat_make_and(menv, trans, curr)

    # v' = 0 if stop & h = 0, -vc/(c+1) if h = 0 & v <= 0 else v - gd
    cond0 = msat_make_and(menv, stop, msat_make_equal(menv, h, _0))
    cond1 = msat_make_and(menv, msat_make_not(menv, stop),
                          msat_make_and(menv, msat_make_equal(menv, h, _0),
                                        msat_make_leq(menv, v, _0)))
    cond2 = msat_make_not(menv, msat_make_and(menv, cond0, cond1))
    m_vc_d_cp1 = msat_make_divide(menv,
                                  msat_make_times(menv, v, c),
                                  msat_make_plus(menv, c, _1))
    m_vc_d_cp1 = msat_make_times(menv, m_1, m_vc_d_cp1)
    v_m_gd = msat_make_minus(menv, v, msat_make_times(menv, g, d))
    curr = msat_make_and(
        menv,
        msat_make_impl(menv, cond0, msat_make_equal(menv, x_v, _0)),
        msat_make_and(menv,
                      msat_make_impl(menv, cond1,
                                     msat_make_equal(menv, x_v, m_vc_d_cp1)),
                      msat_make_impl(menv, cond2,
                                     msat_make_equal(menv, x_v, v_m_gd))))
    trans = msat_make_and(menv, trans, curr)

    # LTL: F G !(h = 0 & v > 0)
    fairness = msat_make_and(menv,
                             msat_make_equal(menv, h, _0),
                             msat_make_gt(menv, v, _0))
    ltl = enc.make_F(enc.make_G(msat_make_not(menv, fairness)))
    return TermMap(curr2next), init, trans, ltl
