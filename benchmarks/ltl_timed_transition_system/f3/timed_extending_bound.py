from collections import Iterable
from math import log, ceil

from mathsat import msat_term, msat_env
from mathsat import msat_make_constant, msat_declare_function
from mathsat import msat_get_integer_type, msat_get_rational_type, \
    msat_get_bool_type
from mathsat import msat_make_and, msat_make_not, msat_make_or, msat_make_iff
from mathsat import msat_make_leq, msat_make_equal, msat_make_true
from mathsat import msat_make_number, msat_make_plus, msat_make_times

from ltl.ltl import TermMap, LTLEncoder
from utils import name_next

delta_name = "delta"


def decl_consts(menv: msat_env, name: str, c_type) -> tuple:
    assert not name.startswith("_"), name
    s = msat_declare_function(menv, name, c_type)
    s = msat_make_constant(menv, s)
    x_s = msat_declare_function(menv, name_next(name), c_type)
    x_s = msat_make_constant(menv, x_s)
    return s, x_s


def make_enum(menv, v_name: str, enum_size: int):
    bool_type = msat_get_bool_type(menv)
    num_bits = ceil(log(enum_size, 2))
    b_vars = []
    for idx in range(num_bits):
        c_name = "{}{}".format(v_name, idx)
        b_vars.append(tuple(decl_consts(menv, c_name, bool_type)))
    vals = []
    x_vals = []
    for enum_val in range(enum_size):
        bit_val = format(enum_val, '0{}b'.format(num_bits))
        assert len(bit_val) == num_bits
        assert all(c in {'0', '1'} for c in bit_val)
        assign = [b_vars[idx] if c == '1' else
                  (msat_make_not(menv, b_vars[idx][0]),
                   msat_make_not(menv, b_vars[idx][1]))
                  for idx, c in enumerate(reversed(bit_val))]
        pred = assign[0][0]
        x_pred = assign[0][1]
        for it in assign[1:]:
            pred = msat_make_and(menv, pred, it[0])
            x_pred = msat_make_and(menv, x_pred, it[1])
        vals.append(pred)
        x_vals.append(x_pred)
    assert len(vals) == enum_size
    assert len(x_vals) == enum_size
    return b_vars, vals, x_vals


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


def check_ltl(menv: msat_env, enc: LTLEncoder) -> (Iterable, msat_term,
                                                   msat_term, msat_term):
    assert menv
    assert isinstance(menv, msat_env)
    assert enc
    assert isinstance(enc, LTLEncoder)
    bool_type = msat_get_bool_type(menv)
    int_type = msat_get_integer_type(menv)
    real_type = msat_get_rational_type(menv)
    c, x_c = decl_consts(menv, "c", real_type)
    bound, x_bound = decl_consts(menv, "bound", int_type)
    delta, x_delta = decl_consts(menv, delta_name, real_type)
    dec_bound, x_dec_bound = decl_consts(menv, "dec_bound", bool_type)

    curr2next = {c: x_c, bound: x_bound, delta: x_delta, dec_bound: x_dec_bound}

    zero = msat_make_number(menv, "0")
    init = dec_bound
    # invar delta >= 0
    init = msat_make_and(menv, init, msat_make_geq(menv, delta, zero))
    trans = msat_make_geq(menv, x_delta, zero)

    # invar c <= bound
    init = msat_make_and(menv, init,
                         msat_make_leq(menv, c, bound))
    trans = msat_make_and(menv, trans,
                          msat_make_leq(menv, x_c, x_bound))

    # delta > 0 -> (c' = c + delta & bound' = bound & dec_bound')
    lhs = msat_make_gt(menv, delta, zero)
    rhs = msat_make_and(menv,
                        msat_make_equal(menv, x_c,
                                        msat_make_plus(menv, c, delta)),
                        msat_make_and(menv, msat_make_equal(menv, x_bound, bound),
                                      x_dec_bound))
    trans = msat_make_and(menv, trans,
                          msat_make_impl(menv, lhs, rhs))
    disc_t = msat_make_equal(menv, delta, zero)
    # c' = c
    trans = msat_make_and(menv, trans,
                          msat_make_impl(menv, disc_t,
                                         msat_make_equal(menv, x_c, c)))
    # c < bound -> (bound' = bound & dec_bound')
    lhs = msat_make_and(menv, disc_t, msat_make_lt(menv, c, bound))
    rhs = msat_make_and(menv, msat_make_equal(menv, x_bound, bound), x_dec_bound)
    trans = msat_make_and(menv, trans,
                          msat_make_impl(menv, lhs, rhs))
    # bound' > bound -> !x_dec_bound
    lhs = msat_make_gt(menv, x_bound, bound)
    rhs = msat_make_not(menv, x_dec_bound)
    trans = msat_make_and(menv, trans,
                          msat_make_impl(menv, lhs, rhs))

    # F G dec_bound
    ltl = enc.make_F(enc.make_G(dec_bound))
    return TermMap(curr2next), init, trans, ltl
