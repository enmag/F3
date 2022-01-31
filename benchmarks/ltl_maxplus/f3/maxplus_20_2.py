
from typing import Iterable, Tuple
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
from expr_utils import name2next


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


def check_ltl(menv: msat_env, enc: LTLEncoder) -> Tuple[Iterable, msat_term,
                                                   msat_term, msat_term]:
    assert menv
    assert isinstance(menv, msat_env)
    assert enc
    assert isinstance(enc, LTLEncoder)

    real_type = msat_get_rational_type(menv)
    names = ["x_0", "x_1", "x_2", "x_3", "x_4", "x_5", "x_6", "x_7", "x_8", "x_9", "x_10", "x_11", "x_12", "x_13", "x_14", "x_15", "x_16", "x_17", "x_18", "x_19"]
    xs = [msat_declare_function(menv, name, real_type)
          for name in names]
    xs = [msat_make_constant(menv, x) for x in xs]

    x_xs = [msat_declare_function(menv, name2next(name), real_type)
            for name in names]
    x_xs = [msat_make_constant(menv, x_x) for x_x in x_xs]

    curr2next = {x: x_x for x, x_x in zip(xs, x_xs)}

    n_10_0 = msat_make_number(menv, "10.0")
    n_11_0 = msat_make_number(menv, "11.0")
    n_12_0 = msat_make_number(menv, "12.0")
    n_13_0 = msat_make_number(menv, "13.0")
    n_14_0 = msat_make_number(menv, "14.0")
    n_15_0 = msat_make_number(menv, "15.0")
    n_16_0 = msat_make_number(menv, "16.0")
    n_17_0 = msat_make_number(menv, "17.0")
    n_18_0 = msat_make_number(menv, "18.0")
    n_19_0 = msat_make_number(menv, "19.0")
    n_1_0 = msat_make_number(menv, "1.0")
    n_20_0 = msat_make_number(menv, "20.0")
    n_2_0 = msat_make_number(menv, "2.0")
    n_3_0 = msat_make_number(menv, "3.0")
    n_4_0 = msat_make_number(menv, "4.0")
    n_5_0 = msat_make_number(menv, "5.0")
    n_6_0 = msat_make_number(menv, "6.0")
    n_7_0 = msat_make_number(menv, "7.0")
    n_8_0 = msat_make_number(menv, "8.0")
    n_9_0 = msat_make_number(menv, "9.0")

    init = msat_make_true(menv)

    trans = msat_make_true(menv)

    # transitions

    expr0 = msat_make_plus(menv, xs[0], n_16_0)
    expr1 = msat_make_plus(menv, xs[1], n_11_0)
    expr2 = msat_make_plus(menv, xs[2], n_14_0)
    expr3 = msat_make_plus(menv, xs[3], n_16_0)
    expr4 = msat_make_plus(menv, xs[6], n_20_0)
    expr5 = msat_make_plus(menv, xs[9], n_17_0)
    expr6 = msat_make_plus(menv, xs[10], n_16_0)
    expr7 = msat_make_plus(menv, xs[14], n_17_0)
    expr8 = msat_make_plus(menv, xs[18], n_11_0)
    expr9 = msat_make_plus(menv, xs[19], n_20_0)
    _t = msat_make_and(menv,
                       msat_make_geq(menv, x_xs[0], expr0),
                       msat_make_geq(menv, x_xs[0], expr1),
                       msat_make_geq(menv, x_xs[0], expr2),
                       msat_make_geq(menv, x_xs[0], expr3),
                       msat_make_geq(menv, x_xs[0], expr4),
                       msat_make_geq(menv, x_xs[0], expr5),
                       msat_make_geq(menv, x_xs[0], expr6),
                       msat_make_geq(menv, x_xs[0], expr7),
                       msat_make_geq(menv, x_xs[0], expr8),
                       msat_make_geq(menv, x_xs[0], expr9),)
    _t = msat_make_and(menv, _t,
                       msat_make_or(menv,
                                    msat_make_equal(menv, x_xs[0], expr0),
                                    msat_make_equal(menv, x_xs[0], expr1),
                                    msat_make_equal(menv, x_xs[0], expr2),
                                    msat_make_equal(menv, x_xs[0], expr3),
                                    msat_make_equal(menv, x_xs[0], expr4),
                                    msat_make_equal(menv, x_xs[0], expr5),
                                    msat_make_equal(menv, x_xs[0], expr6),
                                    msat_make_equal(menv, x_xs[0], expr7),
                                    msat_make_equal(menv, x_xs[0], expr8),
                                    msat_make_equal(menv, x_xs[0], expr9),))
    trans = msat_make_and(menv, trans, _t)

    expr0 = msat_make_plus(menv, xs[1], n_18_0)
    expr1 = msat_make_plus(menv, xs[2], n_3_0)
    expr2 = msat_make_plus(menv, xs[3], n_7_0)
    expr3 = msat_make_plus(menv, xs[4], n_8_0)
    expr4 = msat_make_plus(menv, xs[7], n_16_0)
    expr5 = msat_make_plus(menv, xs[10], n_19_0)
    expr6 = msat_make_plus(menv, xs[11], n_20_0)
    expr7 = msat_make_plus(menv, xs[12], n_15_0)
    expr8 = msat_make_plus(menv, xs[14], n_9_0)
    expr9 = msat_make_plus(menv, xs[16], n_1_0)
    _t = msat_make_and(menv,
                       msat_make_geq(menv, x_xs[1], expr0),
                       msat_make_geq(menv, x_xs[1], expr1),
                       msat_make_geq(menv, x_xs[1], expr2),
                       msat_make_geq(menv, x_xs[1], expr3),
                       msat_make_geq(menv, x_xs[1], expr4),
                       msat_make_geq(menv, x_xs[1], expr5),
                       msat_make_geq(menv, x_xs[1], expr6),
                       msat_make_geq(menv, x_xs[1], expr7),
                       msat_make_geq(menv, x_xs[1], expr8),
                       msat_make_geq(menv, x_xs[1], expr9),)
    _t = msat_make_and(menv, _t,
                       msat_make_or(menv,
                                    msat_make_equal(menv, x_xs[1], expr0),
                                    msat_make_equal(menv, x_xs[1], expr1),
                                    msat_make_equal(menv, x_xs[1], expr2),
                                    msat_make_equal(menv, x_xs[1], expr3),
                                    msat_make_equal(menv, x_xs[1], expr4),
                                    msat_make_equal(menv, x_xs[1], expr5),
                                    msat_make_equal(menv, x_xs[1], expr6),
                                    msat_make_equal(menv, x_xs[1], expr7),
                                    msat_make_equal(menv, x_xs[1], expr8),
                                    msat_make_equal(menv, x_xs[1], expr9),))
    trans = msat_make_and(menv, trans, _t)

    expr0 = msat_make_plus(menv, xs[1], n_16_0)
    expr1 = msat_make_plus(menv, xs[4], n_9_0)
    expr2 = msat_make_plus(menv, xs[6], n_1_0)
    expr3 = msat_make_plus(menv, xs[7], n_12_0)
    expr4 = msat_make_plus(menv, xs[8], n_12_0)
    expr5 = msat_make_plus(menv, xs[11], n_1_0)
    expr6 = msat_make_plus(menv, xs[12], n_9_0)
    expr7 = msat_make_plus(menv, xs[14], n_10_0)
    expr8 = msat_make_plus(menv, xs[15], n_9_0)
    expr9 = msat_make_plus(menv, xs[19], n_15_0)
    _t = msat_make_and(menv,
                       msat_make_geq(menv, x_xs[2], expr0),
                       msat_make_geq(menv, x_xs[2], expr1),
                       msat_make_geq(menv, x_xs[2], expr2),
                       msat_make_geq(menv, x_xs[2], expr3),
                       msat_make_geq(menv, x_xs[2], expr4),
                       msat_make_geq(menv, x_xs[2], expr5),
                       msat_make_geq(menv, x_xs[2], expr6),
                       msat_make_geq(menv, x_xs[2], expr7),
                       msat_make_geq(menv, x_xs[2], expr8),
                       msat_make_geq(menv, x_xs[2], expr9),)
    _t = msat_make_and(menv, _t,
                       msat_make_or(menv,
                                    msat_make_equal(menv, x_xs[2], expr0),
                                    msat_make_equal(menv, x_xs[2], expr1),
                                    msat_make_equal(menv, x_xs[2], expr2),
                                    msat_make_equal(menv, x_xs[2], expr3),
                                    msat_make_equal(menv, x_xs[2], expr4),
                                    msat_make_equal(menv, x_xs[2], expr5),
                                    msat_make_equal(menv, x_xs[2], expr6),
                                    msat_make_equal(menv, x_xs[2], expr7),
                                    msat_make_equal(menv, x_xs[2], expr8),
                                    msat_make_equal(menv, x_xs[2], expr9),))
    trans = msat_make_and(menv, trans, _t)

    expr0 = msat_make_plus(menv, xs[2], n_8_0)
    expr1 = msat_make_plus(menv, xs[4], n_4_0)
    expr2 = msat_make_plus(menv, xs[6], n_1_0)
    expr3 = msat_make_plus(menv, xs[7], n_12_0)
    expr4 = msat_make_plus(menv, xs[8], n_3_0)
    expr5 = msat_make_plus(menv, xs[10], n_18_0)
    expr6 = msat_make_plus(menv, xs[11], n_13_0)
    expr7 = msat_make_plus(menv, xs[12], n_1_0)
    expr8 = msat_make_plus(menv, xs[15], n_15_0)
    expr9 = msat_make_plus(menv, xs[16], n_13_0)
    _t = msat_make_and(menv,
                       msat_make_geq(menv, x_xs[3], expr0),
                       msat_make_geq(menv, x_xs[3], expr1),
                       msat_make_geq(menv, x_xs[3], expr2),
                       msat_make_geq(menv, x_xs[3], expr3),
                       msat_make_geq(menv, x_xs[3], expr4),
                       msat_make_geq(menv, x_xs[3], expr5),
                       msat_make_geq(menv, x_xs[3], expr6),
                       msat_make_geq(menv, x_xs[3], expr7),
                       msat_make_geq(menv, x_xs[3], expr8),
                       msat_make_geq(menv, x_xs[3], expr9),)
    _t = msat_make_and(menv, _t,
                       msat_make_or(menv,
                                    msat_make_equal(menv, x_xs[3], expr0),
                                    msat_make_equal(menv, x_xs[3], expr1),
                                    msat_make_equal(menv, x_xs[3], expr2),
                                    msat_make_equal(menv, x_xs[3], expr3),
                                    msat_make_equal(menv, x_xs[3], expr4),
                                    msat_make_equal(menv, x_xs[3], expr5),
                                    msat_make_equal(menv, x_xs[3], expr6),
                                    msat_make_equal(menv, x_xs[3], expr7),
                                    msat_make_equal(menv, x_xs[3], expr8),
                                    msat_make_equal(menv, x_xs[3], expr9),))
    trans = msat_make_and(menv, trans, _t)

    expr0 = msat_make_plus(menv, xs[0], n_12_0)
    expr1 = msat_make_plus(menv, xs[1], n_17_0)
    expr2 = msat_make_plus(menv, xs[2], n_6_0)
    expr3 = msat_make_plus(menv, xs[4], n_11_0)
    expr4 = msat_make_plus(menv, xs[7], n_11_0)
    expr5 = msat_make_plus(menv, xs[10], n_3_0)
    expr6 = msat_make_plus(menv, xs[11], n_15_0)
    expr7 = msat_make_plus(menv, xs[12], n_3_0)
    expr8 = msat_make_plus(menv, xs[14], n_17_0)
    expr9 = msat_make_plus(menv, xs[17], n_7_0)
    _t = msat_make_and(menv,
                       msat_make_geq(menv, x_xs[4], expr0),
                       msat_make_geq(menv, x_xs[4], expr1),
                       msat_make_geq(menv, x_xs[4], expr2),
                       msat_make_geq(menv, x_xs[4], expr3),
                       msat_make_geq(menv, x_xs[4], expr4),
                       msat_make_geq(menv, x_xs[4], expr5),
                       msat_make_geq(menv, x_xs[4], expr6),
                       msat_make_geq(menv, x_xs[4], expr7),
                       msat_make_geq(menv, x_xs[4], expr8),
                       msat_make_geq(menv, x_xs[4], expr9),)
    _t = msat_make_and(menv, _t,
                       msat_make_or(menv,
                                    msat_make_equal(menv, x_xs[4], expr0),
                                    msat_make_equal(menv, x_xs[4], expr1),
                                    msat_make_equal(menv, x_xs[4], expr2),
                                    msat_make_equal(menv, x_xs[4], expr3),
                                    msat_make_equal(menv, x_xs[4], expr4),
                                    msat_make_equal(menv, x_xs[4], expr5),
                                    msat_make_equal(menv, x_xs[4], expr6),
                                    msat_make_equal(menv, x_xs[4], expr7),
                                    msat_make_equal(menv, x_xs[4], expr8),
                                    msat_make_equal(menv, x_xs[4], expr9),))
    trans = msat_make_and(menv, trans, _t)

    expr0 = msat_make_plus(menv, xs[1], n_20_0)
    expr1 = msat_make_plus(menv, xs[2], n_1_0)
    expr2 = msat_make_plus(menv, xs[5], n_18_0)
    expr3 = msat_make_plus(menv, xs[6], n_10_0)
    expr4 = msat_make_plus(menv, xs[7], n_13_0)
    expr5 = msat_make_plus(menv, xs[10], n_14_0)
    expr6 = msat_make_plus(menv, xs[11], n_9_0)
    expr7 = msat_make_plus(menv, xs[12], n_13_0)
    expr8 = msat_make_plus(menv, xs[16], n_9_0)
    expr9 = msat_make_plus(menv, xs[19], n_17_0)
    _t = msat_make_and(menv,
                       msat_make_geq(menv, x_xs[5], expr0),
                       msat_make_geq(menv, x_xs[5], expr1),
                       msat_make_geq(menv, x_xs[5], expr2),
                       msat_make_geq(menv, x_xs[5], expr3),
                       msat_make_geq(menv, x_xs[5], expr4),
                       msat_make_geq(menv, x_xs[5], expr5),
                       msat_make_geq(menv, x_xs[5], expr6),
                       msat_make_geq(menv, x_xs[5], expr7),
                       msat_make_geq(menv, x_xs[5], expr8),
                       msat_make_geq(menv, x_xs[5], expr9),)
    _t = msat_make_and(menv, _t,
                       msat_make_or(menv,
                                    msat_make_equal(menv, x_xs[5], expr0),
                                    msat_make_equal(menv, x_xs[5], expr1),
                                    msat_make_equal(menv, x_xs[5], expr2),
                                    msat_make_equal(menv, x_xs[5], expr3),
                                    msat_make_equal(menv, x_xs[5], expr4),
                                    msat_make_equal(menv, x_xs[5], expr5),
                                    msat_make_equal(menv, x_xs[5], expr6),
                                    msat_make_equal(menv, x_xs[5], expr7),
                                    msat_make_equal(menv, x_xs[5], expr8),
                                    msat_make_equal(menv, x_xs[5], expr9),))
    trans = msat_make_and(menv, trans, _t)

    expr0 = msat_make_plus(menv, xs[0], n_10_0)
    expr1 = msat_make_plus(menv, xs[2], n_3_0)
    expr2 = msat_make_plus(menv, xs[3], n_14_0)
    expr3 = msat_make_plus(menv, xs[5], n_11_0)
    expr4 = msat_make_plus(menv, xs[8], n_4_0)
    expr5 = msat_make_plus(menv, xs[9], n_9_0)
    expr6 = msat_make_plus(menv, xs[13], n_12_0)
    expr7 = msat_make_plus(menv, xs[17], n_11_0)
    expr8 = msat_make_plus(menv, xs[18], n_19_0)
    expr9 = msat_make_plus(menv, xs[19], n_10_0)
    _t = msat_make_and(menv,
                       msat_make_geq(menv, x_xs[6], expr0),
                       msat_make_geq(menv, x_xs[6], expr1),
                       msat_make_geq(menv, x_xs[6], expr2),
                       msat_make_geq(menv, x_xs[6], expr3),
                       msat_make_geq(menv, x_xs[6], expr4),
                       msat_make_geq(menv, x_xs[6], expr5),
                       msat_make_geq(menv, x_xs[6], expr6),
                       msat_make_geq(menv, x_xs[6], expr7),
                       msat_make_geq(menv, x_xs[6], expr8),
                       msat_make_geq(menv, x_xs[6], expr9),)
    _t = msat_make_and(menv, _t,
                       msat_make_or(menv,
                                    msat_make_equal(menv, x_xs[6], expr0),
                                    msat_make_equal(menv, x_xs[6], expr1),
                                    msat_make_equal(menv, x_xs[6], expr2),
                                    msat_make_equal(menv, x_xs[6], expr3),
                                    msat_make_equal(menv, x_xs[6], expr4),
                                    msat_make_equal(menv, x_xs[6], expr5),
                                    msat_make_equal(menv, x_xs[6], expr6),
                                    msat_make_equal(menv, x_xs[6], expr7),
                                    msat_make_equal(menv, x_xs[6], expr8),
                                    msat_make_equal(menv, x_xs[6], expr9),))
    trans = msat_make_and(menv, trans, _t)

    expr0 = msat_make_plus(menv, xs[1], n_7_0)
    expr1 = msat_make_plus(menv, xs[3], n_15_0)
    expr2 = msat_make_plus(menv, xs[6], n_17_0)
    expr3 = msat_make_plus(menv, xs[7], n_8_0)
    expr4 = msat_make_plus(menv, xs[8], n_11_0)
    expr5 = msat_make_plus(menv, xs[11], n_15_0)
    expr6 = msat_make_plus(menv, xs[12], n_15_0)
    expr7 = msat_make_plus(menv, xs[16], n_20_0)
    expr8 = msat_make_plus(menv, xs[17], n_19_0)
    expr9 = msat_make_plus(menv, xs[19], n_1_0)
    _t = msat_make_and(menv,
                       msat_make_geq(menv, x_xs[7], expr0),
                       msat_make_geq(menv, x_xs[7], expr1),
                       msat_make_geq(menv, x_xs[7], expr2),
                       msat_make_geq(menv, x_xs[7], expr3),
                       msat_make_geq(menv, x_xs[7], expr4),
                       msat_make_geq(menv, x_xs[7], expr5),
                       msat_make_geq(menv, x_xs[7], expr6),
                       msat_make_geq(menv, x_xs[7], expr7),
                       msat_make_geq(menv, x_xs[7], expr8),
                       msat_make_geq(menv, x_xs[7], expr9),)
    _t = msat_make_and(menv, _t,
                       msat_make_or(menv,
                                    msat_make_equal(menv, x_xs[7], expr0),
                                    msat_make_equal(menv, x_xs[7], expr1),
                                    msat_make_equal(menv, x_xs[7], expr2),
                                    msat_make_equal(menv, x_xs[7], expr3),
                                    msat_make_equal(menv, x_xs[7], expr4),
                                    msat_make_equal(menv, x_xs[7], expr5),
                                    msat_make_equal(menv, x_xs[7], expr6),
                                    msat_make_equal(menv, x_xs[7], expr7),
                                    msat_make_equal(menv, x_xs[7], expr8),
                                    msat_make_equal(menv, x_xs[7], expr9),))
    trans = msat_make_and(menv, trans, _t)

    expr0 = msat_make_plus(menv, xs[0], n_4_0)
    expr1 = msat_make_plus(menv, xs[3], n_12_0)
    expr2 = msat_make_plus(menv, xs[4], n_9_0)
    expr3 = msat_make_plus(menv, xs[5], n_12_0)
    expr4 = msat_make_plus(menv, xs[6], n_6_0)
    expr5 = msat_make_plus(menv, xs[9], n_8_0)
    expr6 = msat_make_plus(menv, xs[12], n_11_0)
    expr7 = msat_make_plus(menv, xs[13], n_19_0)
    expr8 = msat_make_plus(menv, xs[15], n_14_0)
    expr9 = msat_make_plus(menv, xs[19], n_7_0)
    _t = msat_make_and(menv,
                       msat_make_geq(menv, x_xs[8], expr0),
                       msat_make_geq(menv, x_xs[8], expr1),
                       msat_make_geq(menv, x_xs[8], expr2),
                       msat_make_geq(menv, x_xs[8], expr3),
                       msat_make_geq(menv, x_xs[8], expr4),
                       msat_make_geq(menv, x_xs[8], expr5),
                       msat_make_geq(menv, x_xs[8], expr6),
                       msat_make_geq(menv, x_xs[8], expr7),
                       msat_make_geq(menv, x_xs[8], expr8),
                       msat_make_geq(menv, x_xs[8], expr9),)
    _t = msat_make_and(menv, _t,
                       msat_make_or(menv,
                                    msat_make_equal(menv, x_xs[8], expr0),
                                    msat_make_equal(menv, x_xs[8], expr1),
                                    msat_make_equal(menv, x_xs[8], expr2),
                                    msat_make_equal(menv, x_xs[8], expr3),
                                    msat_make_equal(menv, x_xs[8], expr4),
                                    msat_make_equal(menv, x_xs[8], expr5),
                                    msat_make_equal(menv, x_xs[8], expr6),
                                    msat_make_equal(menv, x_xs[8], expr7),
                                    msat_make_equal(menv, x_xs[8], expr8),
                                    msat_make_equal(menv, x_xs[8], expr9),))
    trans = msat_make_and(menv, trans, _t)

    expr0 = msat_make_plus(menv, xs[3], n_9_0)
    expr1 = msat_make_plus(menv, xs[4], n_19_0)
    expr2 = msat_make_plus(menv, xs[6], n_13_0)
    expr3 = msat_make_plus(menv, xs[7], n_19_0)
    expr4 = msat_make_plus(menv, xs[8], n_1_0)
    expr5 = msat_make_plus(menv, xs[10], n_11_0)
    expr6 = msat_make_plus(menv, xs[12], n_1_0)
    expr7 = msat_make_plus(menv, xs[15], n_18_0)
    expr8 = msat_make_plus(menv, xs[17], n_1_0)
    expr9 = msat_make_plus(menv, xs[19], n_14_0)
    _t = msat_make_and(menv,
                       msat_make_geq(menv, x_xs[9], expr0),
                       msat_make_geq(menv, x_xs[9], expr1),
                       msat_make_geq(menv, x_xs[9], expr2),
                       msat_make_geq(menv, x_xs[9], expr3),
                       msat_make_geq(menv, x_xs[9], expr4),
                       msat_make_geq(menv, x_xs[9], expr5),
                       msat_make_geq(menv, x_xs[9], expr6),
                       msat_make_geq(menv, x_xs[9], expr7),
                       msat_make_geq(menv, x_xs[9], expr8),
                       msat_make_geq(menv, x_xs[9], expr9),)
    _t = msat_make_and(menv, _t,
                       msat_make_or(menv,
                                    msat_make_equal(menv, x_xs[9], expr0),
                                    msat_make_equal(menv, x_xs[9], expr1),
                                    msat_make_equal(menv, x_xs[9], expr2),
                                    msat_make_equal(menv, x_xs[9], expr3),
                                    msat_make_equal(menv, x_xs[9], expr4),
                                    msat_make_equal(menv, x_xs[9], expr5),
                                    msat_make_equal(menv, x_xs[9], expr6),
                                    msat_make_equal(menv, x_xs[9], expr7),
                                    msat_make_equal(menv, x_xs[9], expr8),
                                    msat_make_equal(menv, x_xs[9], expr9),))
    trans = msat_make_and(menv, trans, _t)

    expr0 = msat_make_plus(menv, xs[0], n_8_0)
    expr1 = msat_make_plus(menv, xs[2], n_9_0)
    expr2 = msat_make_plus(menv, xs[3], n_2_0)
    expr3 = msat_make_plus(menv, xs[4], n_10_0)
    expr4 = msat_make_plus(menv, xs[6], n_4_0)
    expr5 = msat_make_plus(menv, xs[8], n_18_0)
    expr6 = msat_make_plus(menv, xs[10], n_16_0)
    expr7 = msat_make_plus(menv, xs[11], n_8_0)
    expr8 = msat_make_plus(menv, xs[12], n_2_0)
    expr9 = msat_make_plus(menv, xs[19], n_20_0)
    _t = msat_make_and(menv,
                       msat_make_geq(menv, x_xs[10], expr0),
                       msat_make_geq(menv, x_xs[10], expr1),
                       msat_make_geq(menv, x_xs[10], expr2),
                       msat_make_geq(menv, x_xs[10], expr3),
                       msat_make_geq(menv, x_xs[10], expr4),
                       msat_make_geq(menv, x_xs[10], expr5),
                       msat_make_geq(menv, x_xs[10], expr6),
                       msat_make_geq(menv, x_xs[10], expr7),
                       msat_make_geq(menv, x_xs[10], expr8),
                       msat_make_geq(menv, x_xs[10], expr9),)
    _t = msat_make_and(menv, _t,
                       msat_make_or(menv,
                                    msat_make_equal(menv, x_xs[10], expr0),
                                    msat_make_equal(menv, x_xs[10], expr1),
                                    msat_make_equal(menv, x_xs[10], expr2),
                                    msat_make_equal(menv, x_xs[10], expr3),
                                    msat_make_equal(menv, x_xs[10], expr4),
                                    msat_make_equal(menv, x_xs[10], expr5),
                                    msat_make_equal(menv, x_xs[10], expr6),
                                    msat_make_equal(menv, x_xs[10], expr7),
                                    msat_make_equal(menv, x_xs[10], expr8),
                                    msat_make_equal(menv, x_xs[10], expr9),))
    trans = msat_make_and(menv, trans, _t)

    expr0 = msat_make_plus(menv, xs[1], n_5_0)
    expr1 = msat_make_plus(menv, xs[3], n_14_0)
    expr2 = msat_make_plus(menv, xs[4], n_9_0)
    expr3 = msat_make_plus(menv, xs[5], n_5_0)
    expr4 = msat_make_plus(menv, xs[8], n_12_0)
    expr5 = msat_make_plus(menv, xs[10], n_9_0)
    expr6 = msat_make_plus(menv, xs[11], n_16_0)
    expr7 = msat_make_plus(menv, xs[13], n_10_0)
    expr8 = msat_make_plus(menv, xs[14], n_11_0)
    expr9 = msat_make_plus(menv, xs[18], n_18_0)
    _t = msat_make_and(menv,
                       msat_make_geq(menv, x_xs[11], expr0),
                       msat_make_geq(menv, x_xs[11], expr1),
                       msat_make_geq(menv, x_xs[11], expr2),
                       msat_make_geq(menv, x_xs[11], expr3),
                       msat_make_geq(menv, x_xs[11], expr4),
                       msat_make_geq(menv, x_xs[11], expr5),
                       msat_make_geq(menv, x_xs[11], expr6),
                       msat_make_geq(menv, x_xs[11], expr7),
                       msat_make_geq(menv, x_xs[11], expr8),
                       msat_make_geq(menv, x_xs[11], expr9),)
    _t = msat_make_and(menv, _t,
                       msat_make_or(menv,
                                    msat_make_equal(menv, x_xs[11], expr0),
                                    msat_make_equal(menv, x_xs[11], expr1),
                                    msat_make_equal(menv, x_xs[11], expr2),
                                    msat_make_equal(menv, x_xs[11], expr3),
                                    msat_make_equal(menv, x_xs[11], expr4),
                                    msat_make_equal(menv, x_xs[11], expr5),
                                    msat_make_equal(menv, x_xs[11], expr6),
                                    msat_make_equal(menv, x_xs[11], expr7),
                                    msat_make_equal(menv, x_xs[11], expr8),
                                    msat_make_equal(menv, x_xs[11], expr9),))
    trans = msat_make_and(menv, trans, _t)

    expr0 = msat_make_plus(menv, xs[0], n_10_0)
    expr1 = msat_make_plus(menv, xs[3], n_2_0)
    expr2 = msat_make_plus(menv, xs[4], n_18_0)
    expr3 = msat_make_plus(menv, xs[5], n_3_0)
    expr4 = msat_make_plus(menv, xs[7], n_9_0)
    expr5 = msat_make_plus(menv, xs[8], n_16_0)
    expr6 = msat_make_plus(menv, xs[12], n_16_0)
    expr7 = msat_make_plus(menv, xs[13], n_14_0)
    expr8 = msat_make_plus(menv, xs[17], n_20_0)
    expr9 = msat_make_plus(menv, xs[19], n_2_0)
    _t = msat_make_and(menv,
                       msat_make_geq(menv, x_xs[12], expr0),
                       msat_make_geq(menv, x_xs[12], expr1),
                       msat_make_geq(menv, x_xs[12], expr2),
                       msat_make_geq(menv, x_xs[12], expr3),
                       msat_make_geq(menv, x_xs[12], expr4),
                       msat_make_geq(menv, x_xs[12], expr5),
                       msat_make_geq(menv, x_xs[12], expr6),
                       msat_make_geq(menv, x_xs[12], expr7),
                       msat_make_geq(menv, x_xs[12], expr8),
                       msat_make_geq(menv, x_xs[12], expr9),)
    _t = msat_make_and(menv, _t,
                       msat_make_or(menv,
                                    msat_make_equal(menv, x_xs[12], expr0),
                                    msat_make_equal(menv, x_xs[12], expr1),
                                    msat_make_equal(menv, x_xs[12], expr2),
                                    msat_make_equal(menv, x_xs[12], expr3),
                                    msat_make_equal(menv, x_xs[12], expr4),
                                    msat_make_equal(menv, x_xs[12], expr5),
                                    msat_make_equal(menv, x_xs[12], expr6),
                                    msat_make_equal(menv, x_xs[12], expr7),
                                    msat_make_equal(menv, x_xs[12], expr8),
                                    msat_make_equal(menv, x_xs[12], expr9),))
    trans = msat_make_and(menv, trans, _t)

    expr0 = msat_make_plus(menv, xs[0], n_3_0)
    expr1 = msat_make_plus(menv, xs[1], n_9_0)
    expr2 = msat_make_plus(menv, xs[2], n_4_0)
    expr3 = msat_make_plus(menv, xs[3], n_13_0)
    expr4 = msat_make_plus(menv, xs[4], n_18_0)
    expr5 = msat_make_plus(menv, xs[7], n_5_0)
    expr6 = msat_make_plus(menv, xs[8], n_11_0)
    expr7 = msat_make_plus(menv, xs[13], n_4_0)
    expr8 = msat_make_plus(menv, xs[15], n_20_0)
    expr9 = msat_make_plus(menv, xs[17], n_12_0)
    _t = msat_make_and(menv,
                       msat_make_geq(menv, x_xs[13], expr0),
                       msat_make_geq(menv, x_xs[13], expr1),
                       msat_make_geq(menv, x_xs[13], expr2),
                       msat_make_geq(menv, x_xs[13], expr3),
                       msat_make_geq(menv, x_xs[13], expr4),
                       msat_make_geq(menv, x_xs[13], expr5),
                       msat_make_geq(menv, x_xs[13], expr6),
                       msat_make_geq(menv, x_xs[13], expr7),
                       msat_make_geq(menv, x_xs[13], expr8),
                       msat_make_geq(menv, x_xs[13], expr9),)
    _t = msat_make_and(menv, _t,
                       msat_make_or(menv,
                                    msat_make_equal(menv, x_xs[13], expr0),
                                    msat_make_equal(menv, x_xs[13], expr1),
                                    msat_make_equal(menv, x_xs[13], expr2),
                                    msat_make_equal(menv, x_xs[13], expr3),
                                    msat_make_equal(menv, x_xs[13], expr4),
                                    msat_make_equal(menv, x_xs[13], expr5),
                                    msat_make_equal(menv, x_xs[13], expr6),
                                    msat_make_equal(menv, x_xs[13], expr7),
                                    msat_make_equal(menv, x_xs[13], expr8),
                                    msat_make_equal(menv, x_xs[13], expr9),))
    trans = msat_make_and(menv, trans, _t)

    expr0 = msat_make_plus(menv, xs[0], n_3_0)
    expr1 = msat_make_plus(menv, xs[2], n_4_0)
    expr2 = msat_make_plus(menv, xs[5], n_7_0)
    expr3 = msat_make_plus(menv, xs[6], n_15_0)
    expr4 = msat_make_plus(menv, xs[8], n_17_0)
    expr5 = msat_make_plus(menv, xs[9], n_3_0)
    expr6 = msat_make_plus(menv, xs[12], n_10_0)
    expr7 = msat_make_plus(menv, xs[16], n_6_0)
    expr8 = msat_make_plus(menv, xs[17], n_1_0)
    expr9 = msat_make_plus(menv, xs[19], n_2_0)
    _t = msat_make_and(menv,
                       msat_make_geq(menv, x_xs[14], expr0),
                       msat_make_geq(menv, x_xs[14], expr1),
                       msat_make_geq(menv, x_xs[14], expr2),
                       msat_make_geq(menv, x_xs[14], expr3),
                       msat_make_geq(menv, x_xs[14], expr4),
                       msat_make_geq(menv, x_xs[14], expr5),
                       msat_make_geq(menv, x_xs[14], expr6),
                       msat_make_geq(menv, x_xs[14], expr7),
                       msat_make_geq(menv, x_xs[14], expr8),
                       msat_make_geq(menv, x_xs[14], expr9),)
    _t = msat_make_and(menv, _t,
                       msat_make_or(menv,
                                    msat_make_equal(menv, x_xs[14], expr0),
                                    msat_make_equal(menv, x_xs[14], expr1),
                                    msat_make_equal(menv, x_xs[14], expr2),
                                    msat_make_equal(menv, x_xs[14], expr3),
                                    msat_make_equal(menv, x_xs[14], expr4),
                                    msat_make_equal(menv, x_xs[14], expr5),
                                    msat_make_equal(menv, x_xs[14], expr6),
                                    msat_make_equal(menv, x_xs[14], expr7),
                                    msat_make_equal(menv, x_xs[14], expr8),
                                    msat_make_equal(menv, x_xs[14], expr9),))
    trans = msat_make_and(menv, trans, _t)

    expr0 = msat_make_plus(menv, xs[0], n_18_0)
    expr1 = msat_make_plus(menv, xs[2], n_1_0)
    expr2 = msat_make_plus(menv, xs[3], n_12_0)
    expr3 = msat_make_plus(menv, xs[4], n_14_0)
    expr4 = msat_make_plus(menv, xs[7], n_2_0)
    expr5 = msat_make_plus(menv, xs[9], n_19_0)
    expr6 = msat_make_plus(menv, xs[10], n_3_0)
    expr7 = msat_make_plus(menv, xs[14], n_8_0)
    expr8 = msat_make_plus(menv, xs[15], n_3_0)
    expr9 = msat_make_plus(menv, xs[19], n_9_0)
    _t = msat_make_and(menv,
                       msat_make_geq(menv, x_xs[15], expr0),
                       msat_make_geq(menv, x_xs[15], expr1),
                       msat_make_geq(menv, x_xs[15], expr2),
                       msat_make_geq(menv, x_xs[15], expr3),
                       msat_make_geq(menv, x_xs[15], expr4),
                       msat_make_geq(menv, x_xs[15], expr5),
                       msat_make_geq(menv, x_xs[15], expr6),
                       msat_make_geq(menv, x_xs[15], expr7),
                       msat_make_geq(menv, x_xs[15], expr8),
                       msat_make_geq(menv, x_xs[15], expr9),)
    _t = msat_make_and(menv, _t,
                       msat_make_or(menv,
                                    msat_make_equal(menv, x_xs[15], expr0),
                                    msat_make_equal(menv, x_xs[15], expr1),
                                    msat_make_equal(menv, x_xs[15], expr2),
                                    msat_make_equal(menv, x_xs[15], expr3),
                                    msat_make_equal(menv, x_xs[15], expr4),
                                    msat_make_equal(menv, x_xs[15], expr5),
                                    msat_make_equal(menv, x_xs[15], expr6),
                                    msat_make_equal(menv, x_xs[15], expr7),
                                    msat_make_equal(menv, x_xs[15], expr8),
                                    msat_make_equal(menv, x_xs[15], expr9),))
    trans = msat_make_and(menv, trans, _t)

    expr0 = msat_make_plus(menv, xs[1], n_12_0)
    expr1 = msat_make_plus(menv, xs[2], n_8_0)
    expr2 = msat_make_plus(menv, xs[4], n_9_0)
    expr3 = msat_make_plus(menv, xs[5], n_19_0)
    expr4 = msat_make_plus(menv, xs[7], n_14_0)
    expr5 = msat_make_plus(menv, xs[8], n_10_0)
    expr6 = msat_make_plus(menv, xs[9], n_11_0)
    expr7 = msat_make_plus(menv, xs[12], n_12_0)
    expr8 = msat_make_plus(menv, xs[14], n_15_0)
    expr9 = msat_make_plus(menv, xs[17], n_3_0)
    _t = msat_make_and(menv,
                       msat_make_geq(menv, x_xs[16], expr0),
                       msat_make_geq(menv, x_xs[16], expr1),
                       msat_make_geq(menv, x_xs[16], expr2),
                       msat_make_geq(menv, x_xs[16], expr3),
                       msat_make_geq(menv, x_xs[16], expr4),
                       msat_make_geq(menv, x_xs[16], expr5),
                       msat_make_geq(menv, x_xs[16], expr6),
                       msat_make_geq(menv, x_xs[16], expr7),
                       msat_make_geq(menv, x_xs[16], expr8),
                       msat_make_geq(menv, x_xs[16], expr9),)
    _t = msat_make_and(menv, _t,
                       msat_make_or(menv,
                                    msat_make_equal(menv, x_xs[16], expr0),
                                    msat_make_equal(menv, x_xs[16], expr1),
                                    msat_make_equal(menv, x_xs[16], expr2),
                                    msat_make_equal(menv, x_xs[16], expr3),
                                    msat_make_equal(menv, x_xs[16], expr4),
                                    msat_make_equal(menv, x_xs[16], expr5),
                                    msat_make_equal(menv, x_xs[16], expr6),
                                    msat_make_equal(menv, x_xs[16], expr7),
                                    msat_make_equal(menv, x_xs[16], expr8),
                                    msat_make_equal(menv, x_xs[16], expr9),))
    trans = msat_make_and(menv, trans, _t)

    expr0 = msat_make_plus(menv, xs[0], n_10_0)
    expr1 = msat_make_plus(menv, xs[1], n_7_0)
    expr2 = msat_make_plus(menv, xs[2], n_16_0)
    expr3 = msat_make_plus(menv, xs[3], n_8_0)
    expr4 = msat_make_plus(menv, xs[5], n_19_0)
    expr5 = msat_make_plus(menv, xs[6], n_1_0)
    expr6 = msat_make_plus(menv, xs[9], n_16_0)
    expr7 = msat_make_plus(menv, xs[10], n_17_0)
    expr8 = msat_make_plus(menv, xs[11], n_3_0)
    expr9 = msat_make_plus(menv, xs[17], n_20_0)
    _t = msat_make_and(menv,
                       msat_make_geq(menv, x_xs[17], expr0),
                       msat_make_geq(menv, x_xs[17], expr1),
                       msat_make_geq(menv, x_xs[17], expr2),
                       msat_make_geq(menv, x_xs[17], expr3),
                       msat_make_geq(menv, x_xs[17], expr4),
                       msat_make_geq(menv, x_xs[17], expr5),
                       msat_make_geq(menv, x_xs[17], expr6),
                       msat_make_geq(menv, x_xs[17], expr7),
                       msat_make_geq(menv, x_xs[17], expr8),
                       msat_make_geq(menv, x_xs[17], expr9),)
    _t = msat_make_and(menv, _t,
                       msat_make_or(menv,
                                    msat_make_equal(menv, x_xs[17], expr0),
                                    msat_make_equal(menv, x_xs[17], expr1),
                                    msat_make_equal(menv, x_xs[17], expr2),
                                    msat_make_equal(menv, x_xs[17], expr3),
                                    msat_make_equal(menv, x_xs[17], expr4),
                                    msat_make_equal(menv, x_xs[17], expr5),
                                    msat_make_equal(menv, x_xs[17], expr6),
                                    msat_make_equal(menv, x_xs[17], expr7),
                                    msat_make_equal(menv, x_xs[17], expr8),
                                    msat_make_equal(menv, x_xs[17], expr9),))
    trans = msat_make_and(menv, trans, _t)

    expr0 = msat_make_plus(menv, xs[0], n_20_0)
    expr1 = msat_make_plus(menv, xs[1], n_17_0)
    expr2 = msat_make_plus(menv, xs[2], n_13_0)
    expr3 = msat_make_plus(menv, xs[3], n_3_0)
    expr4 = msat_make_plus(menv, xs[4], n_8_0)
    expr5 = msat_make_plus(menv, xs[6], n_6_0)
    expr6 = msat_make_plus(menv, xs[8], n_13_0)
    expr7 = msat_make_plus(menv, xs[12], n_2_0)
    expr8 = msat_make_plus(menv, xs[15], n_5_0)
    expr9 = msat_make_plus(menv, xs[18], n_9_0)
    _t = msat_make_and(menv,
                       msat_make_geq(menv, x_xs[18], expr0),
                       msat_make_geq(menv, x_xs[18], expr1),
                       msat_make_geq(menv, x_xs[18], expr2),
                       msat_make_geq(menv, x_xs[18], expr3),
                       msat_make_geq(menv, x_xs[18], expr4),
                       msat_make_geq(menv, x_xs[18], expr5),
                       msat_make_geq(menv, x_xs[18], expr6),
                       msat_make_geq(menv, x_xs[18], expr7),
                       msat_make_geq(menv, x_xs[18], expr8),
                       msat_make_geq(menv, x_xs[18], expr9),)
    _t = msat_make_and(menv, _t,
                       msat_make_or(menv,
                                    msat_make_equal(menv, x_xs[18], expr0),
                                    msat_make_equal(menv, x_xs[18], expr1),
                                    msat_make_equal(menv, x_xs[18], expr2),
                                    msat_make_equal(menv, x_xs[18], expr3),
                                    msat_make_equal(menv, x_xs[18], expr4),
                                    msat_make_equal(menv, x_xs[18], expr5),
                                    msat_make_equal(menv, x_xs[18], expr6),
                                    msat_make_equal(menv, x_xs[18], expr7),
                                    msat_make_equal(menv, x_xs[18], expr8),
                                    msat_make_equal(menv, x_xs[18], expr9),))
    trans = msat_make_and(menv, trans, _t)

    expr0 = msat_make_plus(menv, xs[2], n_1_0)
    expr1 = msat_make_plus(menv, xs[6], n_2_0)
    expr2 = msat_make_plus(menv, xs[7], n_3_0)
    expr3 = msat_make_plus(menv, xs[8], n_1_0)
    expr4 = msat_make_plus(menv, xs[12], n_2_0)
    expr5 = msat_make_plus(menv, xs[13], n_18_0)
    expr6 = msat_make_plus(menv, xs[14], n_10_0)
    expr7 = msat_make_plus(menv, xs[16], n_5_0)
    expr8 = msat_make_plus(menv, xs[17], n_8_0)
    expr9 = msat_make_plus(menv, xs[19], n_9_0)
    _t = msat_make_and(menv,
                       msat_make_geq(menv, x_xs[19], expr0),
                       msat_make_geq(menv, x_xs[19], expr1),
                       msat_make_geq(menv, x_xs[19], expr2),
                       msat_make_geq(menv, x_xs[19], expr3),
                       msat_make_geq(menv, x_xs[19], expr4),
                       msat_make_geq(menv, x_xs[19], expr5),
                       msat_make_geq(menv, x_xs[19], expr6),
                       msat_make_geq(menv, x_xs[19], expr7),
                       msat_make_geq(menv, x_xs[19], expr8),
                       msat_make_geq(menv, x_xs[19], expr9),)
    _t = msat_make_and(menv, _t,
                       msat_make_or(menv,
                                    msat_make_equal(menv, x_xs[19], expr0),
                                    msat_make_equal(menv, x_xs[19], expr1),
                                    msat_make_equal(menv, x_xs[19], expr2),
                                    msat_make_equal(menv, x_xs[19], expr3),
                                    msat_make_equal(menv, x_xs[19], expr4),
                                    msat_make_equal(menv, x_xs[19], expr5),
                                    msat_make_equal(menv, x_xs[19], expr6),
                                    msat_make_equal(menv, x_xs[19], expr7),
                                    msat_make_equal(menv, x_xs[19], expr8),
                                    msat_make_equal(menv, x_xs[19], expr9),))
    trans = msat_make_and(menv, trans, _t)

    # ltl property: (! ((! (G (x_13 - x_2 >= -20))) U (! (X (x_1 - x_11 > 3)))))
    ltl = msat_make_not(menv, enc.make_U(msat_make_not(menv, enc.make_G(msat_make_geq(menv, msat_make_minus(menv, xs[13], xs[2]), msat_make_number(menv, "-20")))), msat_make_not(menv, enc.make_X(msat_make_gt(menv, msat_make_minus(menv, xs[1], xs[11]), msat_make_number(menv, "3"))))))

    return TermMap(curr2next), init, trans, ltl
