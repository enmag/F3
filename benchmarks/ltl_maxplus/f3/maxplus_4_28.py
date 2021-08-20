
from collections import Iterable
from mathsat import msat_term, msat_env
from mathsat import msat_make_true, msat_make_false
from mathsat import msat_make_constant, msat_declare_function
from mathsat import msat_get_rational_type
from mathsat import msat_make_and as _msat_make_and
from mathsat import msat_make_or as _msat_make_or
from mathsat import msat_make_not
from mathsat import msat_make_leq, msat_make_equal
from mathsat import msat_make_number, msat_make_plus, msat_make_times
from ltl.ltl import TermMap, LTLEncoder
from utils import name_next


def msat_make_and(menv: msat_env, *args):
    if len(args) == 0:
        return msat_make_true(menv)
    if len(args) == 1:
        return args[0]
    res = _msat_make_and(menv, args[0], args[1])
    for arg in args[2:]:
        res = _msat_make_and(menv, res, arg)
    return res


def msat_make_or(menv: msat_env, *args):
    if len(args) == 0:
        return msat_make_false(menv)
    if len(args) == 1:
        return args[0]
    res = _msat_make_or(menv, args[0], args[1])
    for arg in args[2:]:
        res = _msat_make_or(menv, res, arg)
    return res


def msat_make_minus(menv: msat_env, arg0: msat_term, arg1: msat_term):
    n_m1 = msat_make_number(menv, "-1")
    arg1 = msat_make_times(menv, arg1, n_m1)
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


def check_ltl(menv: msat_env, enc: LTLEncoder) -> (Iterable, msat_term,
                                                   msat_term, msat_term):
    assert menv
    assert isinstance(menv, msat_env)
    assert enc
    assert isinstance(enc, LTLEncoder)

    real_type = msat_get_rational_type(menv)
    names = ["x_0", "x_1", "x_2", "x_3"]
    xs = [msat_declare_function(menv, name, real_type)
          for name in names]
    xs = [msat_make_constant(menv, x) for x in xs]

    x_xs = [msat_declare_function(menv, name_next(name), real_type)
            for name in names]
    x_xs = [msat_make_constant(menv, x_x) for x_x in x_xs]

    curr2next = {x: x_x for x, x_x in zip(xs, x_xs)}

    n_10_0 = msat_make_number(menv, "10.0")
    n_11_0 = msat_make_number(menv, "11.0")
    n_12_0 = msat_make_number(menv, "12.0")
    n_14_0 = msat_make_number(menv, "14.0")
    n_15_0 = msat_make_number(menv, "15.0")
    n_17_0 = msat_make_number(menv, "17.0")
    n_6_0 = msat_make_number(menv, "6.0")

    init = msat_make_true(menv)

    trans = msat_make_true(menv)

    # transitions

    expr0 = msat_make_plus(menv, xs[1], n_12_0)
    expr1 = msat_make_plus(menv, xs[3], n_10_0)
    _t = msat_make_and(menv,
                       msat_make_geq(menv, x_xs[0], expr0),
                       msat_make_geq(menv, x_xs[0], expr1),)
    _t = msat_make_and(menv, _t,
                       msat_make_or(menv,
                                    msat_make_equal(menv, x_xs[0], expr0),
                                    msat_make_equal(menv, x_xs[0], expr1),))
    trans = msat_make_and(menv, trans, _t)

    expr0 = msat_make_plus(menv, xs[1], n_11_0)
    expr1 = msat_make_plus(menv, xs[2], n_14_0)
    _t = msat_make_and(menv,
                       msat_make_geq(menv, x_xs[1], expr0),
                       msat_make_geq(menv, x_xs[1], expr1),)
    _t = msat_make_and(menv, _t,
                       msat_make_or(menv,
                                    msat_make_equal(menv, x_xs[1], expr0),
                                    msat_make_equal(menv, x_xs[1], expr1),))
    trans = msat_make_and(menv, trans, _t)

    expr0 = msat_make_plus(menv, xs[0], n_6_0)
    expr1 = msat_make_plus(menv, xs[2], n_15_0)
    _t = msat_make_and(menv,
                       msat_make_geq(menv, x_xs[2], expr0),
                       msat_make_geq(menv, x_xs[2], expr1),)
    _t = msat_make_and(menv, _t,
                       msat_make_or(menv,
                                    msat_make_equal(menv, x_xs[2], expr0),
                                    msat_make_equal(menv, x_xs[2], expr1),))
    trans = msat_make_and(menv, trans, _t)

    expr0 = msat_make_plus(menv, xs[0], n_17_0)
    expr1 = msat_make_plus(menv, xs[1], n_10_0)
    _t = msat_make_and(menv,
                       msat_make_geq(menv, x_xs[3], expr0),
                       msat_make_geq(menv, x_xs[3], expr1),)
    _t = msat_make_and(menv, _t,
                       msat_make_or(menv,
                                    msat_make_equal(menv, x_xs[3], expr0),
                                    msat_make_equal(menv, x_xs[3], expr1),))
    trans = msat_make_and(menv, trans, _t)

    # ltl property: (X ((x_2 - x_3 >= -1) & (G (x_3 - x_2 > -10))))
    ltl = enc.make_X(msat_make_and(menv, msat_make_geq(menv, msat_make_minus(menv, xs[2], xs[3]), msat_make_number(menv, "-1")), enc.make_G(msat_make_gt(menv, msat_make_minus(menv, xs[3], xs[2]), msat_make_number(menv, "-10")))))

    return TermMap(curr2next), init, trans, ltl
