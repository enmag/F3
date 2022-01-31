from pysmt.environment import Environment as PysmtEnv
import pysmt.typing as types

from mathsat import msat_term, msat_env
from mathsat import msat_make_constant, msat_declare_function
from mathsat import msat_get_rational_type, msat_get_integer_type, \
    msat_get_bool_type
from mathsat import msat_make_and, msat_make_not, msat_make_or, msat_make_iff
from mathsat import msat_make_leq, msat_make_equal, msat_make_true
from mathsat import msat_make_number, msat_make_plus, msat_make_times, \
    msat_make_divide

from ltl.ltl import TermMap, LTLEncoder
from expr_utils import name2next, symb2next
from hint import Hint, Location


delta_name = "delta"


def decl_consts(menv: msat_env, name: str, c_type):
    assert not name.startswith("_"), name
    s = msat_declare_function(menv, name, c_type)
    s = msat_make_constant(menv, s)
    x_s = msat_declare_function(menv, name2next(name), c_type)
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
    real_type = msat_get_rational_type(menv)
    h, x_h = decl_consts(menv, "h", real_type)
    v, x_v = decl_consts(menv, "v", real_type)
    d, x_d = decl_consts(menv, delta_name, real_type)

    curr2next = {h: x_h, v: x_v, d: x_d}

    m_1 = msat_make_number(menv, "-1")
    _0 = msat_make_number(menv, "0")
    _2 = msat_make_number(menv, "2")
    g = msat_make_number(menv, "9.81")

    # init
    init = msat_make_and(menv, msat_make_equal(menv, h, _0),
                         msat_make_equal(menv, v, g))
    # invars
    cond = msat_make_and(menv, msat_make_equal(menv, h, _0),
                         msat_make_lt(menv, v, _0))
    # cond -> delta = 0
    init = msat_make_and(menv, init,
                         msat_make_impl(menv, cond,
                                        msat_make_equal(menv, d, _0)))
    trans = msat_make_impl(menv,
                           msat_make_and(menv, msat_make_equal(menv, x_h, _0),
                                         msat_make_lt(menv, x_v, _0)),
                           msat_make_equal(menv, x_d, _0))
    # delta >= 0
    init = msat_make_and(menv, init,
                         msat_make_geq(menv, d, _0))
    trans = msat_make_and(menv, trans,
                          msat_make_geq(menv, x_d, _0))
    # h >= 0
    init = msat_make_and(menv, init,
                         msat_make_geq(menv, h, _0))
    trans = msat_make_and(menv, trans,
                          msat_make_geq(menv, x_h, _0))

    # transition relation
    # h' = 0 if cond else h + vd - gdd/2
    gdd = msat_make_times(menv, g, msat_make_times(menv, d, d))
    half_gdd = msat_make_divide(menv, gdd, _2)
    h_p_vd_m_halfgdd = msat_make_plus(menv, h, msat_make_times(menv, v, d))
    h_p_vd_m_halfgdd = msat_make_minus(menv, h_p_vd_m_halfgdd, half_gdd)
    curr = msat_make_and(
        menv,
        msat_make_impl(menv, cond,
                       msat_make_equal(menv, x_h, _0)),
        msat_make_impl(menv, msat_make_not(menv, cond),
                       msat_make_equal(menv, x_h, h_p_vd_m_halfgdd)))
    trans = msat_make_and(menv, trans, curr)
    # v' = -v if cond else v - gd
    m_v = msat_make_times(menv, m_1, v)
    v_m_gd = msat_make_minus(menv, v, msat_make_times(menv, g, d))
    curr = msat_make_and(menv,
                         msat_make_impl(menv, cond,
                                        msat_make_equal(menv, x_v, m_v)),
                         msat_make_impl(menv, msat_make_not(menv, cond),
                                        msat_make_equal(menv, x_v, v_m_gd)))
    trans = msat_make_and(menv, trans, curr)

    # F G h != 0
    ltl = enc.make_F(enc.make_G(msat_make_not(menv,
                                              msat_make_equal(menv, h, _0))))
    return TermMap(curr2next), init, trans, ltl


def hints(env: PysmtEnv):
    assert isinstance(env, PysmtEnv)

    mgr = env.formula_manager
    h = mgr.Symbol("h", types.REAL)
    v = mgr.Symbol("v", types.REAL)
    d = mgr.Symbol(delta_name, types.REAL)
    symbs = frozenset([h, v, d])

    m_20 = mgr.Real(-20)
    m_2 = mgr.Real(-2)
    m_1 = mgr.Real(-1)
    r_0 = mgr.Real(0)
    r_2 = mgr.Real(2)
    half = mgr.Div(mgr.Real(1), r_2)

    g = mgr.Div(mgr.Real(981), mgr.Real(100))

    x_h = symb2next(env, h)
    assume = mgr.Or(mgr.Equals(d, r_0),
                    mgr.Equals(d, mgr.Times(mgr.Div(r_2, g), v)))
    loc = Location(env, mgr.Equals(h, r_0), assume,
                   stutterT=mgr.Equals(x_h, h))
    x_h_val = mgr.Equals(x_h,
                         mgr.Plus(h, mgr.Minus(mgr.Times(v, d),
                                               mgr.Times(half, g, d, d))))
    loc.set_progress(0, x_h_val)
    hint_h = Hint("h_h", env, frozenset([h]), symbs)
    hint_h.set_locs([loc])

    x_d = symb2next(env, d)
    loc0 = Location(env, mgr.TRUE())
    loc0.set_progress(1, mgr.Equals(x_d, r_0))
    loc1 = Location(env, mgr.Equals(d, r_0))
    loc1.set_progress(2, mgr.Equals(x_d, r_0))
    loc2 = Location(env, mgr.Equals(d, r_0))
    loc2.set_progress(0, mgr.Equals(x_d, mgr.Times(mgr.Div(r_2, g), v)))
    hint_d = Hint("h_d", env, frozenset([d]), symbs)
    hint_d.set_locs([loc0, loc1, loc2])

    return frozenset([hint_h, hint_d])
