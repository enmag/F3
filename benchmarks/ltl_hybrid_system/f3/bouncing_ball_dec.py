from mathsat import msat_term, msat_env
from mathsat import msat_make_constant, msat_declare_function
from mathsat import msat_get_rational_type, msat_get_integer_type, \
    msat_get_bool_type
from mathsat import msat_make_and, msat_make_not, msat_make_or, msat_make_iff
from mathsat import msat_make_leq, msat_make_equal, msat_make_true
from mathsat import msat_make_number, msat_make_plus, msat_make_times

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

    real_type = msat_get_rational_type(menv)
    d, x_d = decl_consts(menv, delta_name, real_type)
    h, x_h = decl_consts(menv, "h", real_type)
    v, x_v = decl_consts(menv, "v", real_type)

    curr2next = {d: x_d, h: x_h, v: x_v}

    g = msat_make_number(menv, "9.81")
    zero = msat_make_number(menv, "0")
    min_half = msat_make_number(menv, "-0.5")
    half = msat_make_number(menv, "0.5")

    # initial location.
    init = msat_make_and(menv,
                         msat_make_equal(menv, h, zero),
                         msat_make_equal(menv, v, g))

    # transition relation.
    vd = msat_make_times(menv, v, d)
    half_gdd = msat_make_times(menv,
                               msat_make_times(menv, half, g),
                               msat_make_times(menv, d, d))
    n_h = msat_make_plus(menv, h,
                         msat_make_minus(menv, vd, half_gdd))
    n_v = msat_make_minus(menv, v, msat_make_times(menv, g, d))
    h_eq_0 = msat_make_equal(menv, h, zero)
    x_h_eq_0 = msat_make_equal(menv, x_h, zero)
    v_lt_0 = msat_make_lt(menv, v, zero)
    x_v_eq_half_v = msat_make_equal(menv, x_v,
                                    msat_make_times(menv, min_half, v))
    x_h_eq_n_h = msat_make_equal(menv, x_h, n_h)
    x_v_eq_n_v = msat_make_equal(menv, x_v, n_v)
    lhs = msat_make_and(menv, h_eq_0, v_lt_0)
    trans = msat_make_and(
        menv,
        msat_make_impl(menv, lhs,
                       msat_make_and(menv, x_h_eq_0, x_v_eq_half_v)),
        msat_make_impl(menv, msat_make_not(menv, lhs),
                       msat_make_and(menv, x_h_eq_n_h,
                                     x_v_eq_n_v)))
    # LTL: F G h != 0
    ltl = enc.make_F(enc.make_G(msat_make_not(menv, h_eq_0)))

    return TermMap(curr2next), init, trans, ltl



# def transition_system(env: PysmtEnv) -> (frozenset, FNode, FNode, FNode):
#     assert isinstance(env, PysmtEnv)
#     mgr = env.formula_manager
#     h = mgr.Symbol("h", types.REAL)
#     v = mgr.Symbol("v", types.REAL)
#     d = mgr.Symbol(delta_name, types.REAL)
#     x_h = symb_to_next(mgr, h)
#     x_v = symb_to_next(mgr, v)
#     # x_d = symb_to_next(mgr, d)
#     symbols = frozenset([h, v, d])

#     g = mgr.Div(mgr.Real(981), mgr.Real(100))
#     r_0 = mgr.Real(0)
#     min_half = mgr.Div(mgr.Real(-1), mgr.Real(2))
#     half = mgr.Div(mgr.Real(1), mgr.Real(2))

#     # initial location.
#     init = mgr.And(mgr.Equals(h, r_0), mgr.Equals(v, g))

#     # transition relation.
#     n_h = mgr.Plus(h, mgr.Minus(mgr.Times(v, d), mgr.Times(half, g, d, d)))
#     n_v = mgr.Minus(v, mgr.Times(g, d))
#     trans = mgr.And(
#         mgr.Implies(
#             mgr.And(mgr.Equals(h, r_0), mgr.LT(v, r_0)),
#             mgr.And(mgr.Equals(x_h, r_0),
#                     mgr.Equals(x_v, mgr.Times(min_half, v)))),
#         mgr.Implies(mgr.Not(mgr.And(mgr.Equals(h, r_0), mgr.LT(v, r_0))),
#                     mgr.And(mgr.Equals(x_h, n_h), mgr.Equals(x_v, n_v))))

#     # fairness.
#     fairness = mgr.Equals(h, r_0)

#     return symbols, init, trans, fairness
