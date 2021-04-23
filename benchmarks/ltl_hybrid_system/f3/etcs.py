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
    real_type = msat_get_rational_type(menv)
    d, x_d = decl_consts(menv, delta_name, real_type)
    rbc_s, x_rbc_s = decl_consts(menv, "rbc_s", bool_type)
    rbc_m, x_rbc_m = decl_consts(menv, "rbc_m", real_type)
    rbc_d, x_rbc_d = decl_consts(menv, "rbc_d", real_type)
    rbc_v_des, x_rbc_v_des = decl_consts(menv, "rbc_v_des", real_type)
    t_c, x_t_c = decl_consts(menv, "train_c", real_type)
    t_z, x_t_z = decl_consts(menv, "train_z", real_type)
    t_v, x_t_v = decl_consts(menv, "train_v", real_type)
    t_a, x_t_a = decl_consts(menv, "train_a", real_type)

    curr2next = {d: x_d, rbc_s: x_rbc_s, rbc_m: x_rbc_m,
                 rbc_d: x_rbc_d, rbc_v_des: x_rbc_v_des, t_c: x_t_c,
                 t_z: x_t_z, t_v: x_t_v, t_a: x_t_a}

    m_1 = msat_make_number(menv, "-1")
    _0 = msat_make_number(menv, "0")
    _1 = msat_make_number(menv, "1")
    _2 = msat_make_number(menv, "2")
    _4 = msat_make_number(menv, "4")
    max_brake = _2
    max_acc = _4
    period = _1
    rbc_brake = rbc_s
    x_rbc_brake = x_rbc_s
    x_rbc_drive = msat_make_not(menv, x_rbc_s)

    # SB := (pow(v, 2) - pow(rbc.d, 2)) / (2 * max_brake) + (max_acc / max_brake + 1) * (max_acc / 2 * pow(period, 2) + period * v);
    v2 = msat_make_times(menv, t_v, t_v)
    rbc_d2 = msat_make_times(menv, rbc_d, rbc_d)
    v2_m_rbc_d2 = msat_make_minus(menv, v2, rbc_d2)
    max_brake_t_2 = msat_make_times(menv, max_brake, _2)
    max_acc_d_max_brake_p_1 = msat_make_plus(menv, _1,
                                             msat_make_divide(menv, max_acc,
                                                              max_brake))
    period2_t_2 = msat_make_times(menv, _2, msat_make_times(menv, period, period))
    max_acc_div_2_period2 = msat_make_divide(menv, max_acc, period2_t_2)
    period_v = msat_make_times(menv, period, t_v)
    t_SB = msat_make_divide(menv, v2_m_rbc_d2, max_brake_t_2)
    t_SB = msat_make_plus(menv, t_SB,
                          msat_make_times(menv, max_acc_d_max_brake_p_1,
                                          max_acc_div_2_period2))
    t_SB = msat_make_plus(menv, t_SB, period_v)

    # init rbc_s = brake & rbc_v_des = 0 & t_z < rbc_m & t_v = 0 & t_a = 0 & t_c = 0
    init = msat_make_and(
        menv,
        msat_make_and(menv, rbc_brake,
                      msat_make_equal(menv, rbc_v_des, _0)),
        msat_make_and(menv,
                      msat_make_and(menv,
                                    msat_make_lt(menv, t_z, rbc_m),
                                    msat_make_equal(menv, t_v, _0)),
                      msat_make_and(menv, msat_make_equal(menv, t_a, _0),
                                    msat_make_equal(menv, t_c, _0))))
    # invar: delta >= 0 & rbc_m >= 0 & rbc_d >= 0 & rbc_v_des >= 0
    invar = msat_make_and(menv,
                          msat_make_and(menv,
                                        msat_make_geq(menv, d, _0),
                                        msat_make_geq(menv, rbc_m, _0)),
                          msat_make_and(menv,
                                        msat_make_geq(menv, rbc_d, _0),
                                        msat_make_geq(menv, rbc_v_des, _0)))
    init = msat_make_and(menv, init, invar)
    trans = msat_make_and(menv,
                          msat_make_and(menv,
                                        msat_make_geq(menv, x_d, _0),
                                        msat_make_geq(menv, x_rbc_m, _0)),
                          msat_make_and(menv,
                                        msat_make_geq(menv, x_rbc_d, _0),
                                        msat_make_geq(menv, x_rbc_v_des, _0)))
    # invar: t_c <= period & t_z >= 0 & t_a >= -max_brake & t_a <= max_acc
    invar = msat_make_and(
        menv,
        msat_make_and(menv,
                      msat_make_leq(menv, t_c, period),
                      msat_make_geq(menv, t_z, _0)),
        msat_make_and(menv,
                      msat_make_geq(menv, t_a,
                                    msat_make_times(menv, m_1, max_brake)),
                      msat_make_leq(menv, t_a, max_acc)))
    init = msat_make_and(menv, init, invar)
    invar = msat_make_and(
        menv,
        msat_make_and(menv,
                      msat_make_leq(menv, x_t_c, period),
                      msat_make_geq(menv, x_t_z, _0)),
        msat_make_and(menv,
                      msat_make_geq(menv, x_t_a,
                                    msat_make_times(menv, m_1, max_brake)),
                      msat_make_leq(menv, x_t_a, max_acc)))
    trans = msat_make_and(menv, trans, invar)
    # invar: (t_v >= rbc_v_des -> t_a <= 0)
    init = msat_make_and(menv, init,
                         msat_make_impl(menv,
                                        msat_make_geq(menv, t_v, rbc_v_des),
                                        msat_make_leq(menv, t_a, _0)))
    trans = msat_make_and(menv, trans,
                          msat_make_impl(menv,
                                         msat_make_geq(menv, x_t_v, x_rbc_v_des),
                                         msat_make_leq(menv, x_t_a, _0)))
    # transition relation
    # rbc_brake' -> rbc_m' = rbc_m & rbc_d' = rbc_d
    lhs = x_rbc_brake
    rhs = msat_make_and(menv,
                        msat_make_equal(menv, x_rbc_m, rbc_m),
                        msat_make_equal(menv, x_rbc_d, rbc_d))
    trans = msat_make_and(menv, trans,
                          msat_make_impl(menv, lhs, rhs))
    # rbc_drive' -> rbc_drbc_d - rbc_d'rbc_d' <= 2 max_brake (rbc_m' - rbc_m)
    lhs = x_rbc_drive
    d2_diff = msat_make_minus(menv,
                              msat_make_times(menv, rbc_d, rbc_d),
                              msat_make_times(menv, x_rbc_d, x_rbc_d))
    m_diff = msat_make_minus(menv, x_rbc_m, rbc_m)
    max_brake_2_m_diff = msat_make_times(menv,
                                         msat_make_times(menv, _2, max_brake),
                                         m_diff)
    rhs = msat_make_leq(menv, d2_diff, max_brake_2_m_diff)
    trans = msat_make_and(menv, trans,
                          msat_make_impl(menv, lhs, rhs))
    # t_c < period -> t_c' = t_c + d;
    lhs = msat_make_lt(menv, t_c, period)
    rhs = msat_make_equal(menv, x_t_c, msat_make_plus(menv, t_c, d))
    trans = msat_make_and(menv, trans,
                          msat_make_impl(menv, lhs, rhs))
    # t_c >= period -> t_c' = 0 & d = 0;
    lhs = msat_make_geq(menv, t_c, period)
    rhs = msat_make_and(menv,
                        msat_make_equal(menv, t_c, _0),
                        msat_make_equal(menv, d, _0))
    trans = msat_make_and(menv, trans,
                          msat_make_impl(menv, lhs, rhs))
    # t_z = z + vd + add/2
    add = msat_make_times(menv, t_a, msat_make_times(menv, d, d))
    rhs = msat_make_plus(menv, msat_make_times(menv, t_v, d),
                         msat_make_divide(menv, add, _2))
    rhs = msat_make_plus(menv, t_z, rhs)
    trans = msat_make_and(menv, trans,
                          msat_make_equal(menv, x_t_z, rhs))
    # t_v' = t_v + t_a d
    curr = msat_make_equal(menv, x_t_v,
                           msat_make_plus(menv, t_v,
                                          msat_make_times(menv, t_a, d)))
    trans = msat_make_and(menv, trans, curr)
    # cond := t_c = period & t_c' = 0
    cond = msat_make_and(menv, msat_make_equal(menv, t_c, period),
                         msat_make_equal(menv, x_t_c, _0))
    # cond & (rbc_m - t_z <= t_SB | rbc_brake) -> t_a' = - max_brake
    disj0 = msat_make_leq(menv,
                          msat_make_minus(menv, rbc_m, t_z),
                          t_SB)
    lhs = msat_make_and(menv, cond,
                        msat_make_or(menv, disj0, rbc_brake))
    rhs = msat_make_equal(menv, x_t_a,
                          msat_make_times(menv, m_1, max_brake))
    trans = msat_make_and(menv, trans,
                          msat_make_impl(menv, lhs, rhs))

    # LTL F G !(delta > 0 & t_v > 0)
    fairness = msat_make_and(menv, msat_make_gt(menv, d, _0),
                             msat_make_gt(menv, t_v, _0))
    ltl = enc.make_F(enc.make_G(msat_make_not(menv, fairness)))

    return TermMap(curr2next), init, trans, ltl
