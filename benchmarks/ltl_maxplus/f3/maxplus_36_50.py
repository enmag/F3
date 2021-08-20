
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
    names = ["x_0", "x_1", "x_2", "x_3", "x_4", "x_5", "x_6", "x_7", "x_8", "x_9", "x_10", "x_11", "x_12", "x_13", "x_14", "x_15", "x_16", "x_17", "x_18", "x_19", "x_20", "x_21", "x_22", "x_23", "x_24", "x_25", "x_26", "x_27", "x_28", "x_29", "x_30", "x_31", "x_32", "x_33", "x_34", "x_35"]
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

    expr0 = msat_make_plus(menv, xs[1], n_5_0)
    expr1 = msat_make_plus(menv, xs[3], n_1_0)
    expr2 = msat_make_plus(menv, xs[6], n_9_0)
    expr3 = msat_make_plus(menv, xs[7], n_13_0)
    expr4 = msat_make_plus(menv, xs[8], n_5_0)
    expr5 = msat_make_plus(menv, xs[9], n_13_0)
    expr6 = msat_make_plus(menv, xs[10], n_18_0)
    expr7 = msat_make_plus(menv, xs[11], n_6_0)
    expr8 = msat_make_plus(menv, xs[12], n_19_0)
    expr9 = msat_make_plus(menv, xs[13], n_5_0)
    expr10 = msat_make_plus(menv, xs[23], n_15_0)
    expr11 = msat_make_plus(menv, xs[24], n_9_0)
    expr12 = msat_make_plus(menv, xs[25], n_10_0)
    expr13 = msat_make_plus(menv, xs[26], n_1_0)
    expr14 = msat_make_plus(menv, xs[28], n_3_0)
    expr15 = msat_make_plus(menv, xs[29], n_15_0)
    expr16 = msat_make_plus(menv, xs[32], n_1_0)
    expr17 = msat_make_plus(menv, xs[33], n_8_0)
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
                       msat_make_geq(menv, x_xs[0], expr9),
                       msat_make_geq(menv, x_xs[0], expr10),
                       msat_make_geq(menv, x_xs[0], expr11),
                       msat_make_geq(menv, x_xs[0], expr12),
                       msat_make_geq(menv, x_xs[0], expr13),
                       msat_make_geq(menv, x_xs[0], expr14),
                       msat_make_geq(menv, x_xs[0], expr15),
                       msat_make_geq(menv, x_xs[0], expr16),
                       msat_make_geq(menv, x_xs[0], expr17),)
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
                                    msat_make_equal(menv, x_xs[0], expr9),
                                    msat_make_equal(menv, x_xs[0], expr10),
                                    msat_make_equal(menv, x_xs[0], expr11),
                                    msat_make_equal(menv, x_xs[0], expr12),
                                    msat_make_equal(menv, x_xs[0], expr13),
                                    msat_make_equal(menv, x_xs[0], expr14),
                                    msat_make_equal(menv, x_xs[0], expr15),
                                    msat_make_equal(menv, x_xs[0], expr16),
                                    msat_make_equal(menv, x_xs[0], expr17),))
    trans = msat_make_and(menv, trans, _t)

    expr0 = msat_make_plus(menv, xs[1], n_16_0)
    expr1 = msat_make_plus(menv, xs[2], n_9_0)
    expr2 = msat_make_plus(menv, xs[4], n_20_0)
    expr3 = msat_make_plus(menv, xs[6], n_1_0)
    expr4 = msat_make_plus(menv, xs[11], n_2_0)
    expr5 = msat_make_plus(menv, xs[13], n_14_0)
    expr6 = msat_make_plus(menv, xs[15], n_8_0)
    expr7 = msat_make_plus(menv, xs[16], n_20_0)
    expr8 = msat_make_plus(menv, xs[18], n_18_0)
    expr9 = msat_make_plus(menv, xs[19], n_17_0)
    expr10 = msat_make_plus(menv, xs[20], n_17_0)
    expr11 = msat_make_plus(menv, xs[21], n_20_0)
    expr12 = msat_make_plus(menv, xs[24], n_2_0)
    expr13 = msat_make_plus(menv, xs[25], n_3_0)
    expr14 = msat_make_plus(menv, xs[26], n_6_0)
    expr15 = msat_make_plus(menv, xs[27], n_16_0)
    expr16 = msat_make_plus(menv, xs[28], n_14_0)
    expr17 = msat_make_plus(menv, xs[33], n_20_0)
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
                       msat_make_geq(menv, x_xs[1], expr9),
                       msat_make_geq(menv, x_xs[1], expr10),
                       msat_make_geq(menv, x_xs[1], expr11),
                       msat_make_geq(menv, x_xs[1], expr12),
                       msat_make_geq(menv, x_xs[1], expr13),
                       msat_make_geq(menv, x_xs[1], expr14),
                       msat_make_geq(menv, x_xs[1], expr15),
                       msat_make_geq(menv, x_xs[1], expr16),
                       msat_make_geq(menv, x_xs[1], expr17),)
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
                                    msat_make_equal(menv, x_xs[1], expr9),
                                    msat_make_equal(menv, x_xs[1], expr10),
                                    msat_make_equal(menv, x_xs[1], expr11),
                                    msat_make_equal(menv, x_xs[1], expr12),
                                    msat_make_equal(menv, x_xs[1], expr13),
                                    msat_make_equal(menv, x_xs[1], expr14),
                                    msat_make_equal(menv, x_xs[1], expr15),
                                    msat_make_equal(menv, x_xs[1], expr16),
                                    msat_make_equal(menv, x_xs[1], expr17),))
    trans = msat_make_and(menv, trans, _t)

    expr0 = msat_make_plus(menv, xs[0], n_14_0)
    expr1 = msat_make_plus(menv, xs[1], n_9_0)
    expr2 = msat_make_plus(menv, xs[2], n_9_0)
    expr3 = msat_make_plus(menv, xs[4], n_7_0)
    expr4 = msat_make_plus(menv, xs[5], n_11_0)
    expr5 = msat_make_plus(menv, xs[10], n_4_0)
    expr6 = msat_make_plus(menv, xs[11], n_11_0)
    expr7 = msat_make_plus(menv, xs[12], n_14_0)
    expr8 = msat_make_plus(menv, xs[13], n_14_0)
    expr9 = msat_make_plus(menv, xs[16], n_2_0)
    expr10 = msat_make_plus(menv, xs[18], n_19_0)
    expr11 = msat_make_plus(menv, xs[20], n_10_0)
    expr12 = msat_make_plus(menv, xs[24], n_6_0)
    expr13 = msat_make_plus(menv, xs[25], n_10_0)
    expr14 = msat_make_plus(menv, xs[28], n_16_0)
    expr15 = msat_make_plus(menv, xs[32], n_16_0)
    expr16 = msat_make_plus(menv, xs[33], n_1_0)
    expr17 = msat_make_plus(menv, xs[34], n_9_0)
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
                       msat_make_geq(menv, x_xs[2], expr9),
                       msat_make_geq(menv, x_xs[2], expr10),
                       msat_make_geq(menv, x_xs[2], expr11),
                       msat_make_geq(menv, x_xs[2], expr12),
                       msat_make_geq(menv, x_xs[2], expr13),
                       msat_make_geq(menv, x_xs[2], expr14),
                       msat_make_geq(menv, x_xs[2], expr15),
                       msat_make_geq(menv, x_xs[2], expr16),
                       msat_make_geq(menv, x_xs[2], expr17),)
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
                                    msat_make_equal(menv, x_xs[2], expr9),
                                    msat_make_equal(menv, x_xs[2], expr10),
                                    msat_make_equal(menv, x_xs[2], expr11),
                                    msat_make_equal(menv, x_xs[2], expr12),
                                    msat_make_equal(menv, x_xs[2], expr13),
                                    msat_make_equal(menv, x_xs[2], expr14),
                                    msat_make_equal(menv, x_xs[2], expr15),
                                    msat_make_equal(menv, x_xs[2], expr16),
                                    msat_make_equal(menv, x_xs[2], expr17),))
    trans = msat_make_and(menv, trans, _t)

    expr0 = msat_make_plus(menv, xs[1], n_19_0)
    expr1 = msat_make_plus(menv, xs[3], n_9_0)
    expr2 = msat_make_plus(menv, xs[4], n_11_0)
    expr3 = msat_make_plus(menv, xs[5], n_6_0)
    expr4 = msat_make_plus(menv, xs[6], n_10_0)
    expr5 = msat_make_plus(menv, xs[7], n_19_0)
    expr6 = msat_make_plus(menv, xs[10], n_3_0)
    expr7 = msat_make_plus(menv, xs[11], n_19_0)
    expr8 = msat_make_plus(menv, xs[13], n_16_0)
    expr9 = msat_make_plus(menv, xs[14], n_17_0)
    expr10 = msat_make_plus(menv, xs[16], n_11_0)
    expr11 = msat_make_plus(menv, xs[20], n_7_0)
    expr12 = msat_make_plus(menv, xs[22], n_14_0)
    expr13 = msat_make_plus(menv, xs[24], n_16_0)
    expr14 = msat_make_plus(menv, xs[25], n_5_0)
    expr15 = msat_make_plus(menv, xs[28], n_8_0)
    expr16 = msat_make_plus(menv, xs[29], n_14_0)
    expr17 = msat_make_plus(menv, xs[34], n_12_0)
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
                       msat_make_geq(menv, x_xs[3], expr9),
                       msat_make_geq(menv, x_xs[3], expr10),
                       msat_make_geq(menv, x_xs[3], expr11),
                       msat_make_geq(menv, x_xs[3], expr12),
                       msat_make_geq(menv, x_xs[3], expr13),
                       msat_make_geq(menv, x_xs[3], expr14),
                       msat_make_geq(menv, x_xs[3], expr15),
                       msat_make_geq(menv, x_xs[3], expr16),
                       msat_make_geq(menv, x_xs[3], expr17),)
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
                                    msat_make_equal(menv, x_xs[3], expr9),
                                    msat_make_equal(menv, x_xs[3], expr10),
                                    msat_make_equal(menv, x_xs[3], expr11),
                                    msat_make_equal(menv, x_xs[3], expr12),
                                    msat_make_equal(menv, x_xs[3], expr13),
                                    msat_make_equal(menv, x_xs[3], expr14),
                                    msat_make_equal(menv, x_xs[3], expr15),
                                    msat_make_equal(menv, x_xs[3], expr16),
                                    msat_make_equal(menv, x_xs[3], expr17),))
    trans = msat_make_and(menv, trans, _t)

    expr0 = msat_make_plus(menv, xs[0], n_18_0)
    expr1 = msat_make_plus(menv, xs[1], n_7_0)
    expr2 = msat_make_plus(menv, xs[2], n_11_0)
    expr3 = msat_make_plus(menv, xs[4], n_16_0)
    expr4 = msat_make_plus(menv, xs[5], n_14_0)
    expr5 = msat_make_plus(menv, xs[7], n_5_0)
    expr6 = msat_make_plus(menv, xs[11], n_5_0)
    expr7 = msat_make_plus(menv, xs[14], n_15_0)
    expr8 = msat_make_plus(menv, xs[17], n_20_0)
    expr9 = msat_make_plus(menv, xs[19], n_18_0)
    expr10 = msat_make_plus(menv, xs[22], n_14_0)
    expr11 = msat_make_plus(menv, xs[23], n_19_0)
    expr12 = msat_make_plus(menv, xs[24], n_14_0)
    expr13 = msat_make_plus(menv, xs[25], n_7_0)
    expr14 = msat_make_plus(menv, xs[29], n_7_0)
    expr15 = msat_make_plus(menv, xs[30], n_14_0)
    expr16 = msat_make_plus(menv, xs[32], n_7_0)
    expr17 = msat_make_plus(menv, xs[35], n_5_0)
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
                       msat_make_geq(menv, x_xs[4], expr9),
                       msat_make_geq(menv, x_xs[4], expr10),
                       msat_make_geq(menv, x_xs[4], expr11),
                       msat_make_geq(menv, x_xs[4], expr12),
                       msat_make_geq(menv, x_xs[4], expr13),
                       msat_make_geq(menv, x_xs[4], expr14),
                       msat_make_geq(menv, x_xs[4], expr15),
                       msat_make_geq(menv, x_xs[4], expr16),
                       msat_make_geq(menv, x_xs[4], expr17),)
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
                                    msat_make_equal(menv, x_xs[4], expr9),
                                    msat_make_equal(menv, x_xs[4], expr10),
                                    msat_make_equal(menv, x_xs[4], expr11),
                                    msat_make_equal(menv, x_xs[4], expr12),
                                    msat_make_equal(menv, x_xs[4], expr13),
                                    msat_make_equal(menv, x_xs[4], expr14),
                                    msat_make_equal(menv, x_xs[4], expr15),
                                    msat_make_equal(menv, x_xs[4], expr16),
                                    msat_make_equal(menv, x_xs[4], expr17),))
    trans = msat_make_and(menv, trans, _t)

    expr0 = msat_make_plus(menv, xs[0], n_10_0)
    expr1 = msat_make_plus(menv, xs[1], n_7_0)
    expr2 = msat_make_plus(menv, xs[6], n_18_0)
    expr3 = msat_make_plus(menv, xs[7], n_8_0)
    expr4 = msat_make_plus(menv, xs[9], n_10_0)
    expr5 = msat_make_plus(menv, xs[10], n_11_0)
    expr6 = msat_make_plus(menv, xs[11], n_1_0)
    expr7 = msat_make_plus(menv, xs[12], n_3_0)
    expr8 = msat_make_plus(menv, xs[14], n_16_0)
    expr9 = msat_make_plus(menv, xs[16], n_12_0)
    expr10 = msat_make_plus(menv, xs[18], n_20_0)
    expr11 = msat_make_plus(menv, xs[19], n_3_0)
    expr12 = msat_make_plus(menv, xs[22], n_10_0)
    expr13 = msat_make_plus(menv, xs[26], n_6_0)
    expr14 = msat_make_plus(menv, xs[27], n_19_0)
    expr15 = msat_make_plus(menv, xs[29], n_12_0)
    expr16 = msat_make_plus(menv, xs[30], n_17_0)
    expr17 = msat_make_plus(menv, xs[33], n_10_0)
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
                       msat_make_geq(menv, x_xs[5], expr9),
                       msat_make_geq(menv, x_xs[5], expr10),
                       msat_make_geq(menv, x_xs[5], expr11),
                       msat_make_geq(menv, x_xs[5], expr12),
                       msat_make_geq(menv, x_xs[5], expr13),
                       msat_make_geq(menv, x_xs[5], expr14),
                       msat_make_geq(menv, x_xs[5], expr15),
                       msat_make_geq(menv, x_xs[5], expr16),
                       msat_make_geq(menv, x_xs[5], expr17),)
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
                                    msat_make_equal(menv, x_xs[5], expr9),
                                    msat_make_equal(menv, x_xs[5], expr10),
                                    msat_make_equal(menv, x_xs[5], expr11),
                                    msat_make_equal(menv, x_xs[5], expr12),
                                    msat_make_equal(menv, x_xs[5], expr13),
                                    msat_make_equal(menv, x_xs[5], expr14),
                                    msat_make_equal(menv, x_xs[5], expr15),
                                    msat_make_equal(menv, x_xs[5], expr16),
                                    msat_make_equal(menv, x_xs[5], expr17),))
    trans = msat_make_and(menv, trans, _t)

    expr0 = msat_make_plus(menv, xs[1], n_20_0)
    expr1 = msat_make_plus(menv, xs[2], n_1_0)
    expr2 = msat_make_plus(menv, xs[3], n_14_0)
    expr3 = msat_make_plus(menv, xs[7], n_8_0)
    expr4 = msat_make_plus(menv, xs[8], n_15_0)
    expr5 = msat_make_plus(menv, xs[9], n_9_0)
    expr6 = msat_make_plus(menv, xs[11], n_7_0)
    expr7 = msat_make_plus(menv, xs[12], n_17_0)
    expr8 = msat_make_plus(menv, xs[13], n_14_0)
    expr9 = msat_make_plus(menv, xs[14], n_11_0)
    expr10 = msat_make_plus(menv, xs[17], n_11_0)
    expr11 = msat_make_plus(menv, xs[18], n_9_0)
    expr12 = msat_make_plus(menv, xs[25], n_13_0)
    expr13 = msat_make_plus(menv, xs[28], n_13_0)
    expr14 = msat_make_plus(menv, xs[31], n_18_0)
    expr15 = msat_make_plus(menv, xs[32], n_20_0)
    expr16 = msat_make_plus(menv, xs[33], n_10_0)
    expr17 = msat_make_plus(menv, xs[35], n_3_0)
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
                       msat_make_geq(menv, x_xs[6], expr9),
                       msat_make_geq(menv, x_xs[6], expr10),
                       msat_make_geq(menv, x_xs[6], expr11),
                       msat_make_geq(menv, x_xs[6], expr12),
                       msat_make_geq(menv, x_xs[6], expr13),
                       msat_make_geq(menv, x_xs[6], expr14),
                       msat_make_geq(menv, x_xs[6], expr15),
                       msat_make_geq(menv, x_xs[6], expr16),
                       msat_make_geq(menv, x_xs[6], expr17),)
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
                                    msat_make_equal(menv, x_xs[6], expr9),
                                    msat_make_equal(menv, x_xs[6], expr10),
                                    msat_make_equal(menv, x_xs[6], expr11),
                                    msat_make_equal(menv, x_xs[6], expr12),
                                    msat_make_equal(menv, x_xs[6], expr13),
                                    msat_make_equal(menv, x_xs[6], expr14),
                                    msat_make_equal(menv, x_xs[6], expr15),
                                    msat_make_equal(menv, x_xs[6], expr16),
                                    msat_make_equal(menv, x_xs[6], expr17),))
    trans = msat_make_and(menv, trans, _t)

    expr0 = msat_make_plus(menv, xs[1], n_20_0)
    expr1 = msat_make_plus(menv, xs[4], n_18_0)
    expr2 = msat_make_plus(menv, xs[9], n_12_0)
    expr3 = msat_make_plus(menv, xs[10], n_14_0)
    expr4 = msat_make_plus(menv, xs[12], n_8_0)
    expr5 = msat_make_plus(menv, xs[15], n_13_0)
    expr6 = msat_make_plus(menv, xs[16], n_20_0)
    expr7 = msat_make_plus(menv, xs[17], n_7_0)
    expr8 = msat_make_plus(menv, xs[20], n_5_0)
    expr9 = msat_make_plus(menv, xs[21], n_5_0)
    expr10 = msat_make_plus(menv, xs[25], n_8_0)
    expr11 = msat_make_plus(menv, xs[26], n_19_0)
    expr12 = msat_make_plus(menv, xs[27], n_20_0)
    expr13 = msat_make_plus(menv, xs[29], n_15_0)
    expr14 = msat_make_plus(menv, xs[31], n_20_0)
    expr15 = msat_make_plus(menv, xs[33], n_4_0)
    expr16 = msat_make_plus(menv, xs[34], n_3_0)
    expr17 = msat_make_plus(menv, xs[35], n_3_0)
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
                       msat_make_geq(menv, x_xs[7], expr9),
                       msat_make_geq(menv, x_xs[7], expr10),
                       msat_make_geq(menv, x_xs[7], expr11),
                       msat_make_geq(menv, x_xs[7], expr12),
                       msat_make_geq(menv, x_xs[7], expr13),
                       msat_make_geq(menv, x_xs[7], expr14),
                       msat_make_geq(menv, x_xs[7], expr15),
                       msat_make_geq(menv, x_xs[7], expr16),
                       msat_make_geq(menv, x_xs[7], expr17),)
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
                                    msat_make_equal(menv, x_xs[7], expr9),
                                    msat_make_equal(menv, x_xs[7], expr10),
                                    msat_make_equal(menv, x_xs[7], expr11),
                                    msat_make_equal(menv, x_xs[7], expr12),
                                    msat_make_equal(menv, x_xs[7], expr13),
                                    msat_make_equal(menv, x_xs[7], expr14),
                                    msat_make_equal(menv, x_xs[7], expr15),
                                    msat_make_equal(menv, x_xs[7], expr16),
                                    msat_make_equal(menv, x_xs[7], expr17),))
    trans = msat_make_and(menv, trans, _t)

    expr0 = msat_make_plus(menv, xs[2], n_20_0)
    expr1 = msat_make_plus(menv, xs[7], n_12_0)
    expr2 = msat_make_plus(menv, xs[11], n_5_0)
    expr3 = msat_make_plus(menv, xs[13], n_6_0)
    expr4 = msat_make_plus(menv, xs[14], n_10_0)
    expr5 = msat_make_plus(menv, xs[15], n_10_0)
    expr6 = msat_make_plus(menv, xs[16], n_14_0)
    expr7 = msat_make_plus(menv, xs[17], n_16_0)
    expr8 = msat_make_plus(menv, xs[18], n_14_0)
    expr9 = msat_make_plus(menv, xs[19], n_11_0)
    expr10 = msat_make_plus(menv, xs[20], n_17_0)
    expr11 = msat_make_plus(menv, xs[21], n_3_0)
    expr12 = msat_make_plus(menv, xs[23], n_16_0)
    expr13 = msat_make_plus(menv, xs[26], n_1_0)
    expr14 = msat_make_plus(menv, xs[27], n_18_0)
    expr15 = msat_make_plus(menv, xs[31], n_19_0)
    expr16 = msat_make_plus(menv, xs[32], n_4_0)
    expr17 = msat_make_plus(menv, xs[33], n_4_0)
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
                       msat_make_geq(menv, x_xs[8], expr9),
                       msat_make_geq(menv, x_xs[8], expr10),
                       msat_make_geq(menv, x_xs[8], expr11),
                       msat_make_geq(menv, x_xs[8], expr12),
                       msat_make_geq(menv, x_xs[8], expr13),
                       msat_make_geq(menv, x_xs[8], expr14),
                       msat_make_geq(menv, x_xs[8], expr15),
                       msat_make_geq(menv, x_xs[8], expr16),
                       msat_make_geq(menv, x_xs[8], expr17),)
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
                                    msat_make_equal(menv, x_xs[8], expr9),
                                    msat_make_equal(menv, x_xs[8], expr10),
                                    msat_make_equal(menv, x_xs[8], expr11),
                                    msat_make_equal(menv, x_xs[8], expr12),
                                    msat_make_equal(menv, x_xs[8], expr13),
                                    msat_make_equal(menv, x_xs[8], expr14),
                                    msat_make_equal(menv, x_xs[8], expr15),
                                    msat_make_equal(menv, x_xs[8], expr16),
                                    msat_make_equal(menv, x_xs[8], expr17),))
    trans = msat_make_and(menv, trans, _t)

    expr0 = msat_make_plus(menv, xs[1], n_14_0)
    expr1 = msat_make_plus(menv, xs[2], n_15_0)
    expr2 = msat_make_plus(menv, xs[3], n_10_0)
    expr3 = msat_make_plus(menv, xs[5], n_7_0)
    expr4 = msat_make_plus(menv, xs[6], n_8_0)
    expr5 = msat_make_plus(menv, xs[8], n_7_0)
    expr6 = msat_make_plus(menv, xs[10], n_5_0)
    expr7 = msat_make_plus(menv, xs[11], n_9_0)
    expr8 = msat_make_plus(menv, xs[12], n_14_0)
    expr9 = msat_make_plus(menv, xs[15], n_14_0)
    expr10 = msat_make_plus(menv, xs[16], n_14_0)
    expr11 = msat_make_plus(menv, xs[17], n_6_0)
    expr12 = msat_make_plus(menv, xs[19], n_12_0)
    expr13 = msat_make_plus(menv, xs[25], n_11_0)
    expr14 = msat_make_plus(menv, xs[26], n_16_0)
    expr15 = msat_make_plus(menv, xs[29], n_7_0)
    expr16 = msat_make_plus(menv, xs[30], n_2_0)
    expr17 = msat_make_plus(menv, xs[33], n_1_0)
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
                       msat_make_geq(menv, x_xs[9], expr9),
                       msat_make_geq(menv, x_xs[9], expr10),
                       msat_make_geq(menv, x_xs[9], expr11),
                       msat_make_geq(menv, x_xs[9], expr12),
                       msat_make_geq(menv, x_xs[9], expr13),
                       msat_make_geq(menv, x_xs[9], expr14),
                       msat_make_geq(menv, x_xs[9], expr15),
                       msat_make_geq(menv, x_xs[9], expr16),
                       msat_make_geq(menv, x_xs[9], expr17),)
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
                                    msat_make_equal(menv, x_xs[9], expr9),
                                    msat_make_equal(menv, x_xs[9], expr10),
                                    msat_make_equal(menv, x_xs[9], expr11),
                                    msat_make_equal(menv, x_xs[9], expr12),
                                    msat_make_equal(menv, x_xs[9], expr13),
                                    msat_make_equal(menv, x_xs[9], expr14),
                                    msat_make_equal(menv, x_xs[9], expr15),
                                    msat_make_equal(menv, x_xs[9], expr16),
                                    msat_make_equal(menv, x_xs[9], expr17),))
    trans = msat_make_and(menv, trans, _t)

    expr0 = msat_make_plus(menv, xs[0], n_16_0)
    expr1 = msat_make_plus(menv, xs[1], n_11_0)
    expr2 = msat_make_plus(menv, xs[2], n_10_0)
    expr3 = msat_make_plus(menv, xs[3], n_13_0)
    expr4 = msat_make_plus(menv, xs[7], n_16_0)
    expr5 = msat_make_plus(menv, xs[10], n_8_0)
    expr6 = msat_make_plus(menv, xs[11], n_16_0)
    expr7 = msat_make_plus(menv, xs[13], n_16_0)
    expr8 = msat_make_plus(menv, xs[18], n_13_0)
    expr9 = msat_make_plus(menv, xs[19], n_5_0)
    expr10 = msat_make_plus(menv, xs[20], n_1_0)
    expr11 = msat_make_plus(menv, xs[22], n_15_0)
    expr12 = msat_make_plus(menv, xs[23], n_18_0)
    expr13 = msat_make_plus(menv, xs[24], n_16_0)
    expr14 = msat_make_plus(menv, xs[25], n_6_0)
    expr15 = msat_make_plus(menv, xs[26], n_9_0)
    expr16 = msat_make_plus(menv, xs[30], n_3_0)
    expr17 = msat_make_plus(menv, xs[35], n_10_0)
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
                       msat_make_geq(menv, x_xs[10], expr9),
                       msat_make_geq(menv, x_xs[10], expr10),
                       msat_make_geq(menv, x_xs[10], expr11),
                       msat_make_geq(menv, x_xs[10], expr12),
                       msat_make_geq(menv, x_xs[10], expr13),
                       msat_make_geq(menv, x_xs[10], expr14),
                       msat_make_geq(menv, x_xs[10], expr15),
                       msat_make_geq(menv, x_xs[10], expr16),
                       msat_make_geq(menv, x_xs[10], expr17),)
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
                                    msat_make_equal(menv, x_xs[10], expr9),
                                    msat_make_equal(menv, x_xs[10], expr10),
                                    msat_make_equal(menv, x_xs[10], expr11),
                                    msat_make_equal(menv, x_xs[10], expr12),
                                    msat_make_equal(menv, x_xs[10], expr13),
                                    msat_make_equal(menv, x_xs[10], expr14),
                                    msat_make_equal(menv, x_xs[10], expr15),
                                    msat_make_equal(menv, x_xs[10], expr16),
                                    msat_make_equal(menv, x_xs[10], expr17),))
    trans = msat_make_and(menv, trans, _t)

    expr0 = msat_make_plus(menv, xs[2], n_14_0)
    expr1 = msat_make_plus(menv, xs[3], n_18_0)
    expr2 = msat_make_plus(menv, xs[4], n_12_0)
    expr3 = msat_make_plus(menv, xs[8], n_19_0)
    expr4 = msat_make_plus(menv, xs[10], n_15_0)
    expr5 = msat_make_plus(menv, xs[11], n_12_0)
    expr6 = msat_make_plus(menv, xs[12], n_12_0)
    expr7 = msat_make_plus(menv, xs[14], n_2_0)
    expr8 = msat_make_plus(menv, xs[15], n_2_0)
    expr9 = msat_make_plus(menv, xs[18], n_9_0)
    expr10 = msat_make_plus(menv, xs[23], n_18_0)
    expr11 = msat_make_plus(menv, xs[25], n_17_0)
    expr12 = msat_make_plus(menv, xs[26], n_2_0)
    expr13 = msat_make_plus(menv, xs[27], n_13_0)
    expr14 = msat_make_plus(menv, xs[28], n_19_0)
    expr15 = msat_make_plus(menv, xs[29], n_19_0)
    expr16 = msat_make_plus(menv, xs[32], n_2_0)
    expr17 = msat_make_plus(menv, xs[33], n_13_0)
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
                       msat_make_geq(menv, x_xs[11], expr9),
                       msat_make_geq(menv, x_xs[11], expr10),
                       msat_make_geq(menv, x_xs[11], expr11),
                       msat_make_geq(menv, x_xs[11], expr12),
                       msat_make_geq(menv, x_xs[11], expr13),
                       msat_make_geq(menv, x_xs[11], expr14),
                       msat_make_geq(menv, x_xs[11], expr15),
                       msat_make_geq(menv, x_xs[11], expr16),
                       msat_make_geq(menv, x_xs[11], expr17),)
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
                                    msat_make_equal(menv, x_xs[11], expr9),
                                    msat_make_equal(menv, x_xs[11], expr10),
                                    msat_make_equal(menv, x_xs[11], expr11),
                                    msat_make_equal(menv, x_xs[11], expr12),
                                    msat_make_equal(menv, x_xs[11], expr13),
                                    msat_make_equal(menv, x_xs[11], expr14),
                                    msat_make_equal(menv, x_xs[11], expr15),
                                    msat_make_equal(menv, x_xs[11], expr16),
                                    msat_make_equal(menv, x_xs[11], expr17),))
    trans = msat_make_and(menv, trans, _t)

    expr0 = msat_make_plus(menv, xs[0], n_7_0)
    expr1 = msat_make_plus(menv, xs[3], n_16_0)
    expr2 = msat_make_plus(menv, xs[4], n_3_0)
    expr3 = msat_make_plus(menv, xs[5], n_14_0)
    expr4 = msat_make_plus(menv, xs[7], n_8_0)
    expr5 = msat_make_plus(menv, xs[10], n_6_0)
    expr6 = msat_make_plus(menv, xs[13], n_18_0)
    expr7 = msat_make_plus(menv, xs[14], n_14_0)
    expr8 = msat_make_plus(menv, xs[15], n_3_0)
    expr9 = msat_make_plus(menv, xs[16], n_12_0)
    expr10 = msat_make_plus(menv, xs[17], n_7_0)
    expr11 = msat_make_plus(menv, xs[20], n_10_0)
    expr12 = msat_make_plus(menv, xs[21], n_5_0)
    expr13 = msat_make_plus(menv, xs[26], n_5_0)
    expr14 = msat_make_plus(menv, xs[28], n_13_0)
    expr15 = msat_make_plus(menv, xs[32], n_16_0)
    expr16 = msat_make_plus(menv, xs[33], n_8_0)
    expr17 = msat_make_plus(menv, xs[34], n_18_0)
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
                       msat_make_geq(menv, x_xs[12], expr9),
                       msat_make_geq(menv, x_xs[12], expr10),
                       msat_make_geq(menv, x_xs[12], expr11),
                       msat_make_geq(menv, x_xs[12], expr12),
                       msat_make_geq(menv, x_xs[12], expr13),
                       msat_make_geq(menv, x_xs[12], expr14),
                       msat_make_geq(menv, x_xs[12], expr15),
                       msat_make_geq(menv, x_xs[12], expr16),
                       msat_make_geq(menv, x_xs[12], expr17),)
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
                                    msat_make_equal(menv, x_xs[12], expr9),
                                    msat_make_equal(menv, x_xs[12], expr10),
                                    msat_make_equal(menv, x_xs[12], expr11),
                                    msat_make_equal(menv, x_xs[12], expr12),
                                    msat_make_equal(menv, x_xs[12], expr13),
                                    msat_make_equal(menv, x_xs[12], expr14),
                                    msat_make_equal(menv, x_xs[12], expr15),
                                    msat_make_equal(menv, x_xs[12], expr16),
                                    msat_make_equal(menv, x_xs[12], expr17),))
    trans = msat_make_and(menv, trans, _t)

    expr0 = msat_make_plus(menv, xs[2], n_19_0)
    expr1 = msat_make_plus(menv, xs[3], n_12_0)
    expr2 = msat_make_plus(menv, xs[8], n_12_0)
    expr3 = msat_make_plus(menv, xs[11], n_7_0)
    expr4 = msat_make_plus(menv, xs[12], n_16_0)
    expr5 = msat_make_plus(menv, xs[13], n_18_0)
    expr6 = msat_make_plus(menv, xs[14], n_11_0)
    expr7 = msat_make_plus(menv, xs[15], n_6_0)
    expr8 = msat_make_plus(menv, xs[16], n_10_0)
    expr9 = msat_make_plus(menv, xs[17], n_8_0)
    expr10 = msat_make_plus(menv, xs[18], n_16_0)
    expr11 = msat_make_plus(menv, xs[21], n_3_0)
    expr12 = msat_make_plus(menv, xs[22], n_18_0)
    expr13 = msat_make_plus(menv, xs[24], n_10_0)
    expr14 = msat_make_plus(menv, xs[30], n_3_0)
    expr15 = msat_make_plus(menv, xs[32], n_1_0)
    expr16 = msat_make_plus(menv, xs[33], n_6_0)
    expr17 = msat_make_plus(menv, xs[34], n_20_0)
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
                       msat_make_geq(menv, x_xs[13], expr9),
                       msat_make_geq(menv, x_xs[13], expr10),
                       msat_make_geq(menv, x_xs[13], expr11),
                       msat_make_geq(menv, x_xs[13], expr12),
                       msat_make_geq(menv, x_xs[13], expr13),
                       msat_make_geq(menv, x_xs[13], expr14),
                       msat_make_geq(menv, x_xs[13], expr15),
                       msat_make_geq(menv, x_xs[13], expr16),
                       msat_make_geq(menv, x_xs[13], expr17),)
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
                                    msat_make_equal(menv, x_xs[13], expr9),
                                    msat_make_equal(menv, x_xs[13], expr10),
                                    msat_make_equal(menv, x_xs[13], expr11),
                                    msat_make_equal(menv, x_xs[13], expr12),
                                    msat_make_equal(menv, x_xs[13], expr13),
                                    msat_make_equal(menv, x_xs[13], expr14),
                                    msat_make_equal(menv, x_xs[13], expr15),
                                    msat_make_equal(menv, x_xs[13], expr16),
                                    msat_make_equal(menv, x_xs[13], expr17),))
    trans = msat_make_and(menv, trans, _t)

    expr0 = msat_make_plus(menv, xs[1], n_3_0)
    expr1 = msat_make_plus(menv, xs[2], n_8_0)
    expr2 = msat_make_plus(menv, xs[3], n_7_0)
    expr3 = msat_make_plus(menv, xs[4], n_11_0)
    expr4 = msat_make_plus(menv, xs[11], n_9_0)
    expr5 = msat_make_plus(menv, xs[12], n_13_0)
    expr6 = msat_make_plus(menv, xs[13], n_17_0)
    expr7 = msat_make_plus(menv, xs[15], n_10_0)
    expr8 = msat_make_plus(menv, xs[19], n_17_0)
    expr9 = msat_make_plus(menv, xs[23], n_20_0)
    expr10 = msat_make_plus(menv, xs[25], n_9_0)
    expr11 = msat_make_plus(menv, xs[26], n_14_0)
    expr12 = msat_make_plus(menv, xs[27], n_3_0)
    expr13 = msat_make_plus(menv, xs[28], n_20_0)
    expr14 = msat_make_plus(menv, xs[30], n_1_0)
    expr15 = msat_make_plus(menv, xs[31], n_1_0)
    expr16 = msat_make_plus(menv, xs[32], n_13_0)
    expr17 = msat_make_plus(menv, xs[33], n_2_0)
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
                       msat_make_geq(menv, x_xs[14], expr9),
                       msat_make_geq(menv, x_xs[14], expr10),
                       msat_make_geq(menv, x_xs[14], expr11),
                       msat_make_geq(menv, x_xs[14], expr12),
                       msat_make_geq(menv, x_xs[14], expr13),
                       msat_make_geq(menv, x_xs[14], expr14),
                       msat_make_geq(menv, x_xs[14], expr15),
                       msat_make_geq(menv, x_xs[14], expr16),
                       msat_make_geq(menv, x_xs[14], expr17),)
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
                                    msat_make_equal(menv, x_xs[14], expr9),
                                    msat_make_equal(menv, x_xs[14], expr10),
                                    msat_make_equal(menv, x_xs[14], expr11),
                                    msat_make_equal(menv, x_xs[14], expr12),
                                    msat_make_equal(menv, x_xs[14], expr13),
                                    msat_make_equal(menv, x_xs[14], expr14),
                                    msat_make_equal(menv, x_xs[14], expr15),
                                    msat_make_equal(menv, x_xs[14], expr16),
                                    msat_make_equal(menv, x_xs[14], expr17),))
    trans = msat_make_and(menv, trans, _t)

    expr0 = msat_make_plus(menv, xs[0], n_15_0)
    expr1 = msat_make_plus(menv, xs[2], n_7_0)
    expr2 = msat_make_plus(menv, xs[5], n_9_0)
    expr3 = msat_make_plus(menv, xs[7], n_1_0)
    expr4 = msat_make_plus(menv, xs[9], n_4_0)
    expr5 = msat_make_plus(menv, xs[10], n_20_0)
    expr6 = msat_make_plus(menv, xs[12], n_13_0)
    expr7 = msat_make_plus(menv, xs[15], n_1_0)
    expr8 = msat_make_plus(menv, xs[18], n_1_0)
    expr9 = msat_make_plus(menv, xs[20], n_15_0)
    expr10 = msat_make_plus(menv, xs[21], n_7_0)
    expr11 = msat_make_plus(menv, xs[22], n_16_0)
    expr12 = msat_make_plus(menv, xs[23], n_18_0)
    expr13 = msat_make_plus(menv, xs[24], n_19_0)
    expr14 = msat_make_plus(menv, xs[25], n_5_0)
    expr15 = msat_make_plus(menv, xs[29], n_4_0)
    expr16 = msat_make_plus(menv, xs[30], n_11_0)
    expr17 = msat_make_plus(menv, xs[33], n_16_0)
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
                       msat_make_geq(menv, x_xs[15], expr9),
                       msat_make_geq(menv, x_xs[15], expr10),
                       msat_make_geq(menv, x_xs[15], expr11),
                       msat_make_geq(menv, x_xs[15], expr12),
                       msat_make_geq(menv, x_xs[15], expr13),
                       msat_make_geq(menv, x_xs[15], expr14),
                       msat_make_geq(menv, x_xs[15], expr15),
                       msat_make_geq(menv, x_xs[15], expr16),
                       msat_make_geq(menv, x_xs[15], expr17),)
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
                                    msat_make_equal(menv, x_xs[15], expr9),
                                    msat_make_equal(menv, x_xs[15], expr10),
                                    msat_make_equal(menv, x_xs[15], expr11),
                                    msat_make_equal(menv, x_xs[15], expr12),
                                    msat_make_equal(menv, x_xs[15], expr13),
                                    msat_make_equal(menv, x_xs[15], expr14),
                                    msat_make_equal(menv, x_xs[15], expr15),
                                    msat_make_equal(menv, x_xs[15], expr16),
                                    msat_make_equal(menv, x_xs[15], expr17),))
    trans = msat_make_and(menv, trans, _t)

    expr0 = msat_make_plus(menv, xs[1], n_10_0)
    expr1 = msat_make_plus(menv, xs[4], n_20_0)
    expr2 = msat_make_plus(menv, xs[5], n_4_0)
    expr3 = msat_make_plus(menv, xs[7], n_6_0)
    expr4 = msat_make_plus(menv, xs[9], n_7_0)
    expr5 = msat_make_plus(menv, xs[10], n_12_0)
    expr6 = msat_make_plus(menv, xs[11], n_15_0)
    expr7 = msat_make_plus(menv, xs[12], n_6_0)
    expr8 = msat_make_plus(menv, xs[13], n_15_0)
    expr9 = msat_make_plus(menv, xs[17], n_14_0)
    expr10 = msat_make_plus(menv, xs[18], n_2_0)
    expr11 = msat_make_plus(menv, xs[20], n_8_0)
    expr12 = msat_make_plus(menv, xs[25], n_17_0)
    expr13 = msat_make_plus(menv, xs[26], n_19_0)
    expr14 = msat_make_plus(menv, xs[29], n_6_0)
    expr15 = msat_make_plus(menv, xs[32], n_20_0)
    expr16 = msat_make_plus(menv, xs[33], n_6_0)
    expr17 = msat_make_plus(menv, xs[34], n_6_0)
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
                       msat_make_geq(menv, x_xs[16], expr9),
                       msat_make_geq(menv, x_xs[16], expr10),
                       msat_make_geq(menv, x_xs[16], expr11),
                       msat_make_geq(menv, x_xs[16], expr12),
                       msat_make_geq(menv, x_xs[16], expr13),
                       msat_make_geq(menv, x_xs[16], expr14),
                       msat_make_geq(menv, x_xs[16], expr15),
                       msat_make_geq(menv, x_xs[16], expr16),
                       msat_make_geq(menv, x_xs[16], expr17),)
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
                                    msat_make_equal(menv, x_xs[16], expr9),
                                    msat_make_equal(menv, x_xs[16], expr10),
                                    msat_make_equal(menv, x_xs[16], expr11),
                                    msat_make_equal(menv, x_xs[16], expr12),
                                    msat_make_equal(menv, x_xs[16], expr13),
                                    msat_make_equal(menv, x_xs[16], expr14),
                                    msat_make_equal(menv, x_xs[16], expr15),
                                    msat_make_equal(menv, x_xs[16], expr16),
                                    msat_make_equal(menv, x_xs[16], expr17),))
    trans = msat_make_and(menv, trans, _t)

    expr0 = msat_make_plus(menv, xs[0], n_4_0)
    expr1 = msat_make_plus(menv, xs[1], n_14_0)
    expr2 = msat_make_plus(menv, xs[3], n_18_0)
    expr3 = msat_make_plus(menv, xs[4], n_14_0)
    expr4 = msat_make_plus(menv, xs[6], n_12_0)
    expr5 = msat_make_plus(menv, xs[8], n_11_0)
    expr6 = msat_make_plus(menv, xs[9], n_20_0)
    expr7 = msat_make_plus(menv, xs[12], n_1_0)
    expr8 = msat_make_plus(menv, xs[14], n_8_0)
    expr9 = msat_make_plus(menv, xs[15], n_14_0)
    expr10 = msat_make_plus(menv, xs[17], n_17_0)
    expr11 = msat_make_plus(menv, xs[18], n_17_0)
    expr12 = msat_make_plus(menv, xs[20], n_15_0)
    expr13 = msat_make_plus(menv, xs[25], n_6_0)
    expr14 = msat_make_plus(menv, xs[28], n_15_0)
    expr15 = msat_make_plus(menv, xs[32], n_19_0)
    expr16 = msat_make_plus(menv, xs[33], n_13_0)
    expr17 = msat_make_plus(menv, xs[35], n_9_0)
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
                       msat_make_geq(menv, x_xs[17], expr9),
                       msat_make_geq(menv, x_xs[17], expr10),
                       msat_make_geq(menv, x_xs[17], expr11),
                       msat_make_geq(menv, x_xs[17], expr12),
                       msat_make_geq(menv, x_xs[17], expr13),
                       msat_make_geq(menv, x_xs[17], expr14),
                       msat_make_geq(menv, x_xs[17], expr15),
                       msat_make_geq(menv, x_xs[17], expr16),
                       msat_make_geq(menv, x_xs[17], expr17),)
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
                                    msat_make_equal(menv, x_xs[17], expr9),
                                    msat_make_equal(menv, x_xs[17], expr10),
                                    msat_make_equal(menv, x_xs[17], expr11),
                                    msat_make_equal(menv, x_xs[17], expr12),
                                    msat_make_equal(menv, x_xs[17], expr13),
                                    msat_make_equal(menv, x_xs[17], expr14),
                                    msat_make_equal(menv, x_xs[17], expr15),
                                    msat_make_equal(menv, x_xs[17], expr16),
                                    msat_make_equal(menv, x_xs[17], expr17),))
    trans = msat_make_and(menv, trans, _t)

    expr0 = msat_make_plus(menv, xs[3], n_3_0)
    expr1 = msat_make_plus(menv, xs[7], n_7_0)
    expr2 = msat_make_plus(menv, xs[8], n_12_0)
    expr3 = msat_make_plus(menv, xs[9], n_19_0)
    expr4 = msat_make_plus(menv, xs[10], n_11_0)
    expr5 = msat_make_plus(menv, xs[11], n_1_0)
    expr6 = msat_make_plus(menv, xs[12], n_15_0)
    expr7 = msat_make_plus(menv, xs[14], n_12_0)
    expr8 = msat_make_plus(menv, xs[18], n_17_0)
    expr9 = msat_make_plus(menv, xs[20], n_8_0)
    expr10 = msat_make_plus(menv, xs[21], n_19_0)
    expr11 = msat_make_plus(menv, xs[22], n_3_0)
    expr12 = msat_make_plus(menv, xs[23], n_14_0)
    expr13 = msat_make_plus(menv, xs[25], n_6_0)
    expr14 = msat_make_plus(menv, xs[26], n_20_0)
    expr15 = msat_make_plus(menv, xs[27], n_5_0)
    expr16 = msat_make_plus(menv, xs[28], n_9_0)
    expr17 = msat_make_plus(menv, xs[35], n_4_0)
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
                       msat_make_geq(menv, x_xs[18], expr9),
                       msat_make_geq(menv, x_xs[18], expr10),
                       msat_make_geq(menv, x_xs[18], expr11),
                       msat_make_geq(menv, x_xs[18], expr12),
                       msat_make_geq(menv, x_xs[18], expr13),
                       msat_make_geq(menv, x_xs[18], expr14),
                       msat_make_geq(menv, x_xs[18], expr15),
                       msat_make_geq(menv, x_xs[18], expr16),
                       msat_make_geq(menv, x_xs[18], expr17),)
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
                                    msat_make_equal(menv, x_xs[18], expr9),
                                    msat_make_equal(menv, x_xs[18], expr10),
                                    msat_make_equal(menv, x_xs[18], expr11),
                                    msat_make_equal(menv, x_xs[18], expr12),
                                    msat_make_equal(menv, x_xs[18], expr13),
                                    msat_make_equal(menv, x_xs[18], expr14),
                                    msat_make_equal(menv, x_xs[18], expr15),
                                    msat_make_equal(menv, x_xs[18], expr16),
                                    msat_make_equal(menv, x_xs[18], expr17),))
    trans = msat_make_and(menv, trans, _t)

    expr0 = msat_make_plus(menv, xs[0], n_17_0)
    expr1 = msat_make_plus(menv, xs[1], n_4_0)
    expr2 = msat_make_plus(menv, xs[5], n_19_0)
    expr3 = msat_make_plus(menv, xs[8], n_6_0)
    expr4 = msat_make_plus(menv, xs[9], n_12_0)
    expr5 = msat_make_plus(menv, xs[12], n_10_0)
    expr6 = msat_make_plus(menv, xs[13], n_6_0)
    expr7 = msat_make_plus(menv, xs[15], n_19_0)
    expr8 = msat_make_plus(menv, xs[17], n_8_0)
    expr9 = msat_make_plus(menv, xs[19], n_10_0)
    expr10 = msat_make_plus(menv, xs[20], n_8_0)
    expr11 = msat_make_plus(menv, xs[21], n_19_0)
    expr12 = msat_make_plus(menv, xs[26], n_5_0)
    expr13 = msat_make_plus(menv, xs[28], n_6_0)
    expr14 = msat_make_plus(menv, xs[29], n_17_0)
    expr15 = msat_make_plus(menv, xs[30], n_8_0)
    expr16 = msat_make_plus(menv, xs[31], n_20_0)
    expr17 = msat_make_plus(menv, xs[35], n_14_0)
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
                       msat_make_geq(menv, x_xs[19], expr9),
                       msat_make_geq(menv, x_xs[19], expr10),
                       msat_make_geq(menv, x_xs[19], expr11),
                       msat_make_geq(menv, x_xs[19], expr12),
                       msat_make_geq(menv, x_xs[19], expr13),
                       msat_make_geq(menv, x_xs[19], expr14),
                       msat_make_geq(menv, x_xs[19], expr15),
                       msat_make_geq(menv, x_xs[19], expr16),
                       msat_make_geq(menv, x_xs[19], expr17),)
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
                                    msat_make_equal(menv, x_xs[19], expr9),
                                    msat_make_equal(menv, x_xs[19], expr10),
                                    msat_make_equal(menv, x_xs[19], expr11),
                                    msat_make_equal(menv, x_xs[19], expr12),
                                    msat_make_equal(menv, x_xs[19], expr13),
                                    msat_make_equal(menv, x_xs[19], expr14),
                                    msat_make_equal(menv, x_xs[19], expr15),
                                    msat_make_equal(menv, x_xs[19], expr16),
                                    msat_make_equal(menv, x_xs[19], expr17),))
    trans = msat_make_and(menv, trans, _t)

    expr0 = msat_make_plus(menv, xs[0], n_1_0)
    expr1 = msat_make_plus(menv, xs[3], n_12_0)
    expr2 = msat_make_plus(menv, xs[6], n_7_0)
    expr3 = msat_make_plus(menv, xs[7], n_7_0)
    expr4 = msat_make_plus(menv, xs[8], n_17_0)
    expr5 = msat_make_plus(menv, xs[9], n_16_0)
    expr6 = msat_make_plus(menv, xs[10], n_3_0)
    expr7 = msat_make_plus(menv, xs[11], n_5_0)
    expr8 = msat_make_plus(menv, xs[12], n_5_0)
    expr9 = msat_make_plus(menv, xs[13], n_12_0)
    expr10 = msat_make_plus(menv, xs[17], n_1_0)
    expr11 = msat_make_plus(menv, xs[18], n_2_0)
    expr12 = msat_make_plus(menv, xs[21], n_16_0)
    expr13 = msat_make_plus(menv, xs[27], n_9_0)
    expr14 = msat_make_plus(menv, xs[28], n_11_0)
    expr15 = msat_make_plus(menv, xs[29], n_7_0)
    expr16 = msat_make_plus(menv, xs[34], n_18_0)
    expr17 = msat_make_plus(menv, xs[35], n_12_0)
    _t = msat_make_and(menv,
                       msat_make_geq(menv, x_xs[20], expr0),
                       msat_make_geq(menv, x_xs[20], expr1),
                       msat_make_geq(menv, x_xs[20], expr2),
                       msat_make_geq(menv, x_xs[20], expr3),
                       msat_make_geq(menv, x_xs[20], expr4),
                       msat_make_geq(menv, x_xs[20], expr5),
                       msat_make_geq(menv, x_xs[20], expr6),
                       msat_make_geq(menv, x_xs[20], expr7),
                       msat_make_geq(menv, x_xs[20], expr8),
                       msat_make_geq(menv, x_xs[20], expr9),
                       msat_make_geq(menv, x_xs[20], expr10),
                       msat_make_geq(menv, x_xs[20], expr11),
                       msat_make_geq(menv, x_xs[20], expr12),
                       msat_make_geq(menv, x_xs[20], expr13),
                       msat_make_geq(menv, x_xs[20], expr14),
                       msat_make_geq(menv, x_xs[20], expr15),
                       msat_make_geq(menv, x_xs[20], expr16),
                       msat_make_geq(menv, x_xs[20], expr17),)
    _t = msat_make_and(menv, _t,
                       msat_make_or(menv,
                                    msat_make_equal(menv, x_xs[20], expr0),
                                    msat_make_equal(menv, x_xs[20], expr1),
                                    msat_make_equal(menv, x_xs[20], expr2),
                                    msat_make_equal(menv, x_xs[20], expr3),
                                    msat_make_equal(menv, x_xs[20], expr4),
                                    msat_make_equal(menv, x_xs[20], expr5),
                                    msat_make_equal(menv, x_xs[20], expr6),
                                    msat_make_equal(menv, x_xs[20], expr7),
                                    msat_make_equal(menv, x_xs[20], expr8),
                                    msat_make_equal(menv, x_xs[20], expr9),
                                    msat_make_equal(menv, x_xs[20], expr10),
                                    msat_make_equal(menv, x_xs[20], expr11),
                                    msat_make_equal(menv, x_xs[20], expr12),
                                    msat_make_equal(menv, x_xs[20], expr13),
                                    msat_make_equal(menv, x_xs[20], expr14),
                                    msat_make_equal(menv, x_xs[20], expr15),
                                    msat_make_equal(menv, x_xs[20], expr16),
                                    msat_make_equal(menv, x_xs[20], expr17),))
    trans = msat_make_and(menv, trans, _t)

    expr0 = msat_make_plus(menv, xs[0], n_8_0)
    expr1 = msat_make_plus(menv, xs[2], n_15_0)
    expr2 = msat_make_plus(menv, xs[3], n_17_0)
    expr3 = msat_make_plus(menv, xs[4], n_18_0)
    expr4 = msat_make_plus(menv, xs[6], n_15_0)
    expr5 = msat_make_plus(menv, xs[8], n_9_0)
    expr6 = msat_make_plus(menv, xs[10], n_2_0)
    expr7 = msat_make_plus(menv, xs[12], n_15_0)
    expr8 = msat_make_plus(menv, xs[13], n_4_0)
    expr9 = msat_make_plus(menv, xs[14], n_6_0)
    expr10 = msat_make_plus(menv, xs[15], n_7_0)
    expr11 = msat_make_plus(menv, xs[18], n_19_0)
    expr12 = msat_make_plus(menv, xs[19], n_20_0)
    expr13 = msat_make_plus(menv, xs[21], n_6_0)
    expr14 = msat_make_plus(menv, xs[22], n_15_0)
    expr15 = msat_make_plus(menv, xs[25], n_4_0)
    expr16 = msat_make_plus(menv, xs[27], n_18_0)
    expr17 = msat_make_plus(menv, xs[31], n_10_0)
    _t = msat_make_and(menv,
                       msat_make_geq(menv, x_xs[21], expr0),
                       msat_make_geq(menv, x_xs[21], expr1),
                       msat_make_geq(menv, x_xs[21], expr2),
                       msat_make_geq(menv, x_xs[21], expr3),
                       msat_make_geq(menv, x_xs[21], expr4),
                       msat_make_geq(menv, x_xs[21], expr5),
                       msat_make_geq(menv, x_xs[21], expr6),
                       msat_make_geq(menv, x_xs[21], expr7),
                       msat_make_geq(menv, x_xs[21], expr8),
                       msat_make_geq(menv, x_xs[21], expr9),
                       msat_make_geq(menv, x_xs[21], expr10),
                       msat_make_geq(menv, x_xs[21], expr11),
                       msat_make_geq(menv, x_xs[21], expr12),
                       msat_make_geq(menv, x_xs[21], expr13),
                       msat_make_geq(menv, x_xs[21], expr14),
                       msat_make_geq(menv, x_xs[21], expr15),
                       msat_make_geq(menv, x_xs[21], expr16),
                       msat_make_geq(menv, x_xs[21], expr17),)
    _t = msat_make_and(menv, _t,
                       msat_make_or(menv,
                                    msat_make_equal(menv, x_xs[21], expr0),
                                    msat_make_equal(menv, x_xs[21], expr1),
                                    msat_make_equal(menv, x_xs[21], expr2),
                                    msat_make_equal(menv, x_xs[21], expr3),
                                    msat_make_equal(menv, x_xs[21], expr4),
                                    msat_make_equal(menv, x_xs[21], expr5),
                                    msat_make_equal(menv, x_xs[21], expr6),
                                    msat_make_equal(menv, x_xs[21], expr7),
                                    msat_make_equal(menv, x_xs[21], expr8),
                                    msat_make_equal(menv, x_xs[21], expr9),
                                    msat_make_equal(menv, x_xs[21], expr10),
                                    msat_make_equal(menv, x_xs[21], expr11),
                                    msat_make_equal(menv, x_xs[21], expr12),
                                    msat_make_equal(menv, x_xs[21], expr13),
                                    msat_make_equal(menv, x_xs[21], expr14),
                                    msat_make_equal(menv, x_xs[21], expr15),
                                    msat_make_equal(menv, x_xs[21], expr16),
                                    msat_make_equal(menv, x_xs[21], expr17),))
    trans = msat_make_and(menv, trans, _t)

    expr0 = msat_make_plus(menv, xs[0], n_20_0)
    expr1 = msat_make_plus(menv, xs[2], n_7_0)
    expr2 = msat_make_plus(menv, xs[3], n_12_0)
    expr3 = msat_make_plus(menv, xs[6], n_7_0)
    expr4 = msat_make_plus(menv, xs[12], n_19_0)
    expr5 = msat_make_plus(menv, xs[13], n_6_0)
    expr6 = msat_make_plus(menv, xs[15], n_10_0)
    expr7 = msat_make_plus(menv, xs[16], n_3_0)
    expr8 = msat_make_plus(menv, xs[18], n_10_0)
    expr9 = msat_make_plus(menv, xs[19], n_17_0)
    expr10 = msat_make_plus(menv, xs[21], n_10_0)
    expr11 = msat_make_plus(menv, xs[22], n_13_0)
    expr12 = msat_make_plus(menv, xs[23], n_14_0)
    expr13 = msat_make_plus(menv, xs[24], n_20_0)
    expr14 = msat_make_plus(menv, xs[25], n_11_0)
    expr15 = msat_make_plus(menv, xs[31], n_13_0)
    expr16 = msat_make_plus(menv, xs[33], n_20_0)
    expr17 = msat_make_plus(menv, xs[34], n_10_0)
    _t = msat_make_and(menv,
                       msat_make_geq(menv, x_xs[22], expr0),
                       msat_make_geq(menv, x_xs[22], expr1),
                       msat_make_geq(menv, x_xs[22], expr2),
                       msat_make_geq(menv, x_xs[22], expr3),
                       msat_make_geq(menv, x_xs[22], expr4),
                       msat_make_geq(menv, x_xs[22], expr5),
                       msat_make_geq(menv, x_xs[22], expr6),
                       msat_make_geq(menv, x_xs[22], expr7),
                       msat_make_geq(menv, x_xs[22], expr8),
                       msat_make_geq(menv, x_xs[22], expr9),
                       msat_make_geq(menv, x_xs[22], expr10),
                       msat_make_geq(menv, x_xs[22], expr11),
                       msat_make_geq(menv, x_xs[22], expr12),
                       msat_make_geq(menv, x_xs[22], expr13),
                       msat_make_geq(menv, x_xs[22], expr14),
                       msat_make_geq(menv, x_xs[22], expr15),
                       msat_make_geq(menv, x_xs[22], expr16),
                       msat_make_geq(menv, x_xs[22], expr17),)
    _t = msat_make_and(menv, _t,
                       msat_make_or(menv,
                                    msat_make_equal(menv, x_xs[22], expr0),
                                    msat_make_equal(menv, x_xs[22], expr1),
                                    msat_make_equal(menv, x_xs[22], expr2),
                                    msat_make_equal(menv, x_xs[22], expr3),
                                    msat_make_equal(menv, x_xs[22], expr4),
                                    msat_make_equal(menv, x_xs[22], expr5),
                                    msat_make_equal(menv, x_xs[22], expr6),
                                    msat_make_equal(menv, x_xs[22], expr7),
                                    msat_make_equal(menv, x_xs[22], expr8),
                                    msat_make_equal(menv, x_xs[22], expr9),
                                    msat_make_equal(menv, x_xs[22], expr10),
                                    msat_make_equal(menv, x_xs[22], expr11),
                                    msat_make_equal(menv, x_xs[22], expr12),
                                    msat_make_equal(menv, x_xs[22], expr13),
                                    msat_make_equal(menv, x_xs[22], expr14),
                                    msat_make_equal(menv, x_xs[22], expr15),
                                    msat_make_equal(menv, x_xs[22], expr16),
                                    msat_make_equal(menv, x_xs[22], expr17),))
    trans = msat_make_and(menv, trans, _t)

    expr0 = msat_make_plus(menv, xs[0], n_5_0)
    expr1 = msat_make_plus(menv, xs[3], n_16_0)
    expr2 = msat_make_plus(menv, xs[6], n_10_0)
    expr3 = msat_make_plus(menv, xs[7], n_2_0)
    expr4 = msat_make_plus(menv, xs[9], n_14_0)
    expr5 = msat_make_plus(menv, xs[11], n_20_0)
    expr6 = msat_make_plus(menv, xs[13], n_10_0)
    expr7 = msat_make_plus(menv, xs[18], n_4_0)
    expr8 = msat_make_plus(menv, xs[19], n_11_0)
    expr9 = msat_make_plus(menv, xs[20], n_2_0)
    expr10 = msat_make_plus(menv, xs[23], n_18_0)
    expr11 = msat_make_plus(menv, xs[24], n_16_0)
    expr12 = msat_make_plus(menv, xs[25], n_1_0)
    expr13 = msat_make_plus(menv, xs[27], n_9_0)
    expr14 = msat_make_plus(menv, xs[28], n_2_0)
    expr15 = msat_make_plus(menv, xs[30], n_3_0)
    expr16 = msat_make_plus(menv, xs[31], n_11_0)
    expr17 = msat_make_plus(menv, xs[35], n_7_0)
    _t = msat_make_and(menv,
                       msat_make_geq(menv, x_xs[23], expr0),
                       msat_make_geq(menv, x_xs[23], expr1),
                       msat_make_geq(menv, x_xs[23], expr2),
                       msat_make_geq(menv, x_xs[23], expr3),
                       msat_make_geq(menv, x_xs[23], expr4),
                       msat_make_geq(menv, x_xs[23], expr5),
                       msat_make_geq(menv, x_xs[23], expr6),
                       msat_make_geq(menv, x_xs[23], expr7),
                       msat_make_geq(menv, x_xs[23], expr8),
                       msat_make_geq(menv, x_xs[23], expr9),
                       msat_make_geq(menv, x_xs[23], expr10),
                       msat_make_geq(menv, x_xs[23], expr11),
                       msat_make_geq(menv, x_xs[23], expr12),
                       msat_make_geq(menv, x_xs[23], expr13),
                       msat_make_geq(menv, x_xs[23], expr14),
                       msat_make_geq(menv, x_xs[23], expr15),
                       msat_make_geq(menv, x_xs[23], expr16),
                       msat_make_geq(menv, x_xs[23], expr17),)
    _t = msat_make_and(menv, _t,
                       msat_make_or(menv,
                                    msat_make_equal(menv, x_xs[23], expr0),
                                    msat_make_equal(menv, x_xs[23], expr1),
                                    msat_make_equal(menv, x_xs[23], expr2),
                                    msat_make_equal(menv, x_xs[23], expr3),
                                    msat_make_equal(menv, x_xs[23], expr4),
                                    msat_make_equal(menv, x_xs[23], expr5),
                                    msat_make_equal(menv, x_xs[23], expr6),
                                    msat_make_equal(menv, x_xs[23], expr7),
                                    msat_make_equal(menv, x_xs[23], expr8),
                                    msat_make_equal(menv, x_xs[23], expr9),
                                    msat_make_equal(menv, x_xs[23], expr10),
                                    msat_make_equal(menv, x_xs[23], expr11),
                                    msat_make_equal(menv, x_xs[23], expr12),
                                    msat_make_equal(menv, x_xs[23], expr13),
                                    msat_make_equal(menv, x_xs[23], expr14),
                                    msat_make_equal(menv, x_xs[23], expr15),
                                    msat_make_equal(menv, x_xs[23], expr16),
                                    msat_make_equal(menv, x_xs[23], expr17),))
    trans = msat_make_and(menv, trans, _t)

    expr0 = msat_make_plus(menv, xs[1], n_19_0)
    expr1 = msat_make_plus(menv, xs[3], n_11_0)
    expr2 = msat_make_plus(menv, xs[5], n_14_0)
    expr3 = msat_make_plus(menv, xs[6], n_6_0)
    expr4 = msat_make_plus(menv, xs[8], n_20_0)
    expr5 = msat_make_plus(menv, xs[9], n_1_0)
    expr6 = msat_make_plus(menv, xs[10], n_16_0)
    expr7 = msat_make_plus(menv, xs[12], n_2_0)
    expr8 = msat_make_plus(menv, xs[13], n_19_0)
    expr9 = msat_make_plus(menv, xs[15], n_15_0)
    expr10 = msat_make_plus(menv, xs[18], n_14_0)
    expr11 = msat_make_plus(menv, xs[21], n_9_0)
    expr12 = msat_make_plus(menv, xs[22], n_7_0)
    expr13 = msat_make_plus(menv, xs[23], n_19_0)
    expr14 = msat_make_plus(menv, xs[24], n_20_0)
    expr15 = msat_make_plus(menv, xs[27], n_18_0)
    expr16 = msat_make_plus(menv, xs[32], n_12_0)
    expr17 = msat_make_plus(menv, xs[35], n_19_0)
    _t = msat_make_and(menv,
                       msat_make_geq(menv, x_xs[24], expr0),
                       msat_make_geq(menv, x_xs[24], expr1),
                       msat_make_geq(menv, x_xs[24], expr2),
                       msat_make_geq(menv, x_xs[24], expr3),
                       msat_make_geq(menv, x_xs[24], expr4),
                       msat_make_geq(menv, x_xs[24], expr5),
                       msat_make_geq(menv, x_xs[24], expr6),
                       msat_make_geq(menv, x_xs[24], expr7),
                       msat_make_geq(menv, x_xs[24], expr8),
                       msat_make_geq(menv, x_xs[24], expr9),
                       msat_make_geq(menv, x_xs[24], expr10),
                       msat_make_geq(menv, x_xs[24], expr11),
                       msat_make_geq(menv, x_xs[24], expr12),
                       msat_make_geq(menv, x_xs[24], expr13),
                       msat_make_geq(menv, x_xs[24], expr14),
                       msat_make_geq(menv, x_xs[24], expr15),
                       msat_make_geq(menv, x_xs[24], expr16),
                       msat_make_geq(menv, x_xs[24], expr17),)
    _t = msat_make_and(menv, _t,
                       msat_make_or(menv,
                                    msat_make_equal(menv, x_xs[24], expr0),
                                    msat_make_equal(menv, x_xs[24], expr1),
                                    msat_make_equal(menv, x_xs[24], expr2),
                                    msat_make_equal(menv, x_xs[24], expr3),
                                    msat_make_equal(menv, x_xs[24], expr4),
                                    msat_make_equal(menv, x_xs[24], expr5),
                                    msat_make_equal(menv, x_xs[24], expr6),
                                    msat_make_equal(menv, x_xs[24], expr7),
                                    msat_make_equal(menv, x_xs[24], expr8),
                                    msat_make_equal(menv, x_xs[24], expr9),
                                    msat_make_equal(menv, x_xs[24], expr10),
                                    msat_make_equal(menv, x_xs[24], expr11),
                                    msat_make_equal(menv, x_xs[24], expr12),
                                    msat_make_equal(menv, x_xs[24], expr13),
                                    msat_make_equal(menv, x_xs[24], expr14),
                                    msat_make_equal(menv, x_xs[24], expr15),
                                    msat_make_equal(menv, x_xs[24], expr16),
                                    msat_make_equal(menv, x_xs[24], expr17),))
    trans = msat_make_and(menv, trans, _t)

    expr0 = msat_make_plus(menv, xs[0], n_11_0)
    expr1 = msat_make_plus(menv, xs[2], n_16_0)
    expr2 = msat_make_plus(menv, xs[4], n_15_0)
    expr3 = msat_make_plus(menv, xs[6], n_16_0)
    expr4 = msat_make_plus(menv, xs[7], n_9_0)
    expr5 = msat_make_plus(menv, xs[8], n_4_0)
    expr6 = msat_make_plus(menv, xs[12], n_3_0)
    expr7 = msat_make_plus(menv, xs[15], n_17_0)
    expr8 = msat_make_plus(menv, xs[18], n_16_0)
    expr9 = msat_make_plus(menv, xs[20], n_19_0)
    expr10 = msat_make_plus(menv, xs[22], n_18_0)
    expr11 = msat_make_plus(menv, xs[23], n_10_0)
    expr12 = msat_make_plus(menv, xs[24], n_15_0)
    expr13 = msat_make_plus(menv, xs[25], n_15_0)
    expr14 = msat_make_plus(menv, xs[30], n_18_0)
    expr15 = msat_make_plus(menv, xs[31], n_12_0)
    expr16 = msat_make_plus(menv, xs[33], n_11_0)
    expr17 = msat_make_plus(menv, xs[35], n_7_0)
    _t = msat_make_and(menv,
                       msat_make_geq(menv, x_xs[25], expr0),
                       msat_make_geq(menv, x_xs[25], expr1),
                       msat_make_geq(menv, x_xs[25], expr2),
                       msat_make_geq(menv, x_xs[25], expr3),
                       msat_make_geq(menv, x_xs[25], expr4),
                       msat_make_geq(menv, x_xs[25], expr5),
                       msat_make_geq(menv, x_xs[25], expr6),
                       msat_make_geq(menv, x_xs[25], expr7),
                       msat_make_geq(menv, x_xs[25], expr8),
                       msat_make_geq(menv, x_xs[25], expr9),
                       msat_make_geq(menv, x_xs[25], expr10),
                       msat_make_geq(menv, x_xs[25], expr11),
                       msat_make_geq(menv, x_xs[25], expr12),
                       msat_make_geq(menv, x_xs[25], expr13),
                       msat_make_geq(menv, x_xs[25], expr14),
                       msat_make_geq(menv, x_xs[25], expr15),
                       msat_make_geq(menv, x_xs[25], expr16),
                       msat_make_geq(menv, x_xs[25], expr17),)
    _t = msat_make_and(menv, _t,
                       msat_make_or(menv,
                                    msat_make_equal(menv, x_xs[25], expr0),
                                    msat_make_equal(menv, x_xs[25], expr1),
                                    msat_make_equal(menv, x_xs[25], expr2),
                                    msat_make_equal(menv, x_xs[25], expr3),
                                    msat_make_equal(menv, x_xs[25], expr4),
                                    msat_make_equal(menv, x_xs[25], expr5),
                                    msat_make_equal(menv, x_xs[25], expr6),
                                    msat_make_equal(menv, x_xs[25], expr7),
                                    msat_make_equal(menv, x_xs[25], expr8),
                                    msat_make_equal(menv, x_xs[25], expr9),
                                    msat_make_equal(menv, x_xs[25], expr10),
                                    msat_make_equal(menv, x_xs[25], expr11),
                                    msat_make_equal(menv, x_xs[25], expr12),
                                    msat_make_equal(menv, x_xs[25], expr13),
                                    msat_make_equal(menv, x_xs[25], expr14),
                                    msat_make_equal(menv, x_xs[25], expr15),
                                    msat_make_equal(menv, x_xs[25], expr16),
                                    msat_make_equal(menv, x_xs[25], expr17),))
    trans = msat_make_and(menv, trans, _t)

    expr0 = msat_make_plus(menv, xs[0], n_15_0)
    expr1 = msat_make_plus(menv, xs[1], n_12_0)
    expr2 = msat_make_plus(menv, xs[2], n_11_0)
    expr3 = msat_make_plus(menv, xs[6], n_14_0)
    expr4 = msat_make_plus(menv, xs[8], n_11_0)
    expr5 = msat_make_plus(menv, xs[10], n_20_0)
    expr6 = msat_make_plus(menv, xs[11], n_14_0)
    expr7 = msat_make_plus(menv, xs[12], n_18_0)
    expr8 = msat_make_plus(menv, xs[13], n_18_0)
    expr9 = msat_make_plus(menv, xs[14], n_18_0)
    expr10 = msat_make_plus(menv, xs[15], n_20_0)
    expr11 = msat_make_plus(menv, xs[18], n_14_0)
    expr12 = msat_make_plus(menv, xs[23], n_17_0)
    expr13 = msat_make_plus(menv, xs[25], n_9_0)
    expr14 = msat_make_plus(menv, xs[27], n_15_0)
    expr15 = msat_make_plus(menv, xs[28], n_1_0)
    expr16 = msat_make_plus(menv, xs[31], n_15_0)
    expr17 = msat_make_plus(menv, xs[34], n_1_0)
    _t = msat_make_and(menv,
                       msat_make_geq(menv, x_xs[26], expr0),
                       msat_make_geq(menv, x_xs[26], expr1),
                       msat_make_geq(menv, x_xs[26], expr2),
                       msat_make_geq(menv, x_xs[26], expr3),
                       msat_make_geq(menv, x_xs[26], expr4),
                       msat_make_geq(menv, x_xs[26], expr5),
                       msat_make_geq(menv, x_xs[26], expr6),
                       msat_make_geq(menv, x_xs[26], expr7),
                       msat_make_geq(menv, x_xs[26], expr8),
                       msat_make_geq(menv, x_xs[26], expr9),
                       msat_make_geq(menv, x_xs[26], expr10),
                       msat_make_geq(menv, x_xs[26], expr11),
                       msat_make_geq(menv, x_xs[26], expr12),
                       msat_make_geq(menv, x_xs[26], expr13),
                       msat_make_geq(menv, x_xs[26], expr14),
                       msat_make_geq(menv, x_xs[26], expr15),
                       msat_make_geq(menv, x_xs[26], expr16),
                       msat_make_geq(menv, x_xs[26], expr17),)
    _t = msat_make_and(menv, _t,
                       msat_make_or(menv,
                                    msat_make_equal(menv, x_xs[26], expr0),
                                    msat_make_equal(menv, x_xs[26], expr1),
                                    msat_make_equal(menv, x_xs[26], expr2),
                                    msat_make_equal(menv, x_xs[26], expr3),
                                    msat_make_equal(menv, x_xs[26], expr4),
                                    msat_make_equal(menv, x_xs[26], expr5),
                                    msat_make_equal(menv, x_xs[26], expr6),
                                    msat_make_equal(menv, x_xs[26], expr7),
                                    msat_make_equal(menv, x_xs[26], expr8),
                                    msat_make_equal(menv, x_xs[26], expr9),
                                    msat_make_equal(menv, x_xs[26], expr10),
                                    msat_make_equal(menv, x_xs[26], expr11),
                                    msat_make_equal(menv, x_xs[26], expr12),
                                    msat_make_equal(menv, x_xs[26], expr13),
                                    msat_make_equal(menv, x_xs[26], expr14),
                                    msat_make_equal(menv, x_xs[26], expr15),
                                    msat_make_equal(menv, x_xs[26], expr16),
                                    msat_make_equal(menv, x_xs[26], expr17),))
    trans = msat_make_and(menv, trans, _t)

    expr0 = msat_make_plus(menv, xs[2], n_2_0)
    expr1 = msat_make_plus(menv, xs[4], n_14_0)
    expr2 = msat_make_plus(menv, xs[8], n_14_0)
    expr3 = msat_make_plus(menv, xs[9], n_2_0)
    expr4 = msat_make_plus(menv, xs[10], n_15_0)
    expr5 = msat_make_plus(menv, xs[12], n_17_0)
    expr6 = msat_make_plus(menv, xs[15], n_15_0)
    expr7 = msat_make_plus(menv, xs[16], n_12_0)
    expr8 = msat_make_plus(menv, xs[19], n_20_0)
    expr9 = msat_make_plus(menv, xs[22], n_4_0)
    expr10 = msat_make_plus(menv, xs[24], n_7_0)
    expr11 = msat_make_plus(menv, xs[26], n_19_0)
    expr12 = msat_make_plus(menv, xs[27], n_13_0)
    expr13 = msat_make_plus(menv, xs[31], n_2_0)
    expr14 = msat_make_plus(menv, xs[32], n_17_0)
    expr15 = msat_make_plus(menv, xs[33], n_12_0)
    expr16 = msat_make_plus(menv, xs[34], n_10_0)
    expr17 = msat_make_plus(menv, xs[35], n_6_0)
    _t = msat_make_and(menv,
                       msat_make_geq(menv, x_xs[27], expr0),
                       msat_make_geq(menv, x_xs[27], expr1),
                       msat_make_geq(menv, x_xs[27], expr2),
                       msat_make_geq(menv, x_xs[27], expr3),
                       msat_make_geq(menv, x_xs[27], expr4),
                       msat_make_geq(menv, x_xs[27], expr5),
                       msat_make_geq(menv, x_xs[27], expr6),
                       msat_make_geq(menv, x_xs[27], expr7),
                       msat_make_geq(menv, x_xs[27], expr8),
                       msat_make_geq(menv, x_xs[27], expr9),
                       msat_make_geq(menv, x_xs[27], expr10),
                       msat_make_geq(menv, x_xs[27], expr11),
                       msat_make_geq(menv, x_xs[27], expr12),
                       msat_make_geq(menv, x_xs[27], expr13),
                       msat_make_geq(menv, x_xs[27], expr14),
                       msat_make_geq(menv, x_xs[27], expr15),
                       msat_make_geq(menv, x_xs[27], expr16),
                       msat_make_geq(menv, x_xs[27], expr17),)
    _t = msat_make_and(menv, _t,
                       msat_make_or(menv,
                                    msat_make_equal(menv, x_xs[27], expr0),
                                    msat_make_equal(menv, x_xs[27], expr1),
                                    msat_make_equal(menv, x_xs[27], expr2),
                                    msat_make_equal(menv, x_xs[27], expr3),
                                    msat_make_equal(menv, x_xs[27], expr4),
                                    msat_make_equal(menv, x_xs[27], expr5),
                                    msat_make_equal(menv, x_xs[27], expr6),
                                    msat_make_equal(menv, x_xs[27], expr7),
                                    msat_make_equal(menv, x_xs[27], expr8),
                                    msat_make_equal(menv, x_xs[27], expr9),
                                    msat_make_equal(menv, x_xs[27], expr10),
                                    msat_make_equal(menv, x_xs[27], expr11),
                                    msat_make_equal(menv, x_xs[27], expr12),
                                    msat_make_equal(menv, x_xs[27], expr13),
                                    msat_make_equal(menv, x_xs[27], expr14),
                                    msat_make_equal(menv, x_xs[27], expr15),
                                    msat_make_equal(menv, x_xs[27], expr16),
                                    msat_make_equal(menv, x_xs[27], expr17),))
    trans = msat_make_and(menv, trans, _t)

    expr0 = msat_make_plus(menv, xs[0], n_4_0)
    expr1 = msat_make_plus(menv, xs[1], n_5_0)
    expr2 = msat_make_plus(menv, xs[3], n_16_0)
    expr3 = msat_make_plus(menv, xs[4], n_5_0)
    expr4 = msat_make_plus(menv, xs[6], n_12_0)
    expr5 = msat_make_plus(menv, xs[9], n_18_0)
    expr6 = msat_make_plus(menv, xs[10], n_10_0)
    expr7 = msat_make_plus(menv, xs[12], n_20_0)
    expr8 = msat_make_plus(menv, xs[13], n_2_0)
    expr9 = msat_make_plus(menv, xs[18], n_17_0)
    expr10 = msat_make_plus(menv, xs[19], n_10_0)
    expr11 = msat_make_plus(menv, xs[21], n_6_0)
    expr12 = msat_make_plus(menv, xs[23], n_4_0)
    expr13 = msat_make_plus(menv, xs[25], n_14_0)
    expr14 = msat_make_plus(menv, xs[28], n_19_0)
    expr15 = msat_make_plus(menv, xs[30], n_15_0)
    expr16 = msat_make_plus(menv, xs[31], n_8_0)
    expr17 = msat_make_plus(menv, xs[32], n_2_0)
    _t = msat_make_and(menv,
                       msat_make_geq(menv, x_xs[28], expr0),
                       msat_make_geq(menv, x_xs[28], expr1),
                       msat_make_geq(menv, x_xs[28], expr2),
                       msat_make_geq(menv, x_xs[28], expr3),
                       msat_make_geq(menv, x_xs[28], expr4),
                       msat_make_geq(menv, x_xs[28], expr5),
                       msat_make_geq(menv, x_xs[28], expr6),
                       msat_make_geq(menv, x_xs[28], expr7),
                       msat_make_geq(menv, x_xs[28], expr8),
                       msat_make_geq(menv, x_xs[28], expr9),
                       msat_make_geq(menv, x_xs[28], expr10),
                       msat_make_geq(menv, x_xs[28], expr11),
                       msat_make_geq(menv, x_xs[28], expr12),
                       msat_make_geq(menv, x_xs[28], expr13),
                       msat_make_geq(menv, x_xs[28], expr14),
                       msat_make_geq(menv, x_xs[28], expr15),
                       msat_make_geq(menv, x_xs[28], expr16),
                       msat_make_geq(menv, x_xs[28], expr17),)
    _t = msat_make_and(menv, _t,
                       msat_make_or(menv,
                                    msat_make_equal(menv, x_xs[28], expr0),
                                    msat_make_equal(menv, x_xs[28], expr1),
                                    msat_make_equal(menv, x_xs[28], expr2),
                                    msat_make_equal(menv, x_xs[28], expr3),
                                    msat_make_equal(menv, x_xs[28], expr4),
                                    msat_make_equal(menv, x_xs[28], expr5),
                                    msat_make_equal(menv, x_xs[28], expr6),
                                    msat_make_equal(menv, x_xs[28], expr7),
                                    msat_make_equal(menv, x_xs[28], expr8),
                                    msat_make_equal(menv, x_xs[28], expr9),
                                    msat_make_equal(menv, x_xs[28], expr10),
                                    msat_make_equal(menv, x_xs[28], expr11),
                                    msat_make_equal(menv, x_xs[28], expr12),
                                    msat_make_equal(menv, x_xs[28], expr13),
                                    msat_make_equal(menv, x_xs[28], expr14),
                                    msat_make_equal(menv, x_xs[28], expr15),
                                    msat_make_equal(menv, x_xs[28], expr16),
                                    msat_make_equal(menv, x_xs[28], expr17),))
    trans = msat_make_and(menv, trans, _t)

    expr0 = msat_make_plus(menv, xs[1], n_4_0)
    expr1 = msat_make_plus(menv, xs[2], n_14_0)
    expr2 = msat_make_plus(menv, xs[5], n_16_0)
    expr3 = msat_make_plus(menv, xs[8], n_16_0)
    expr4 = msat_make_plus(menv, xs[9], n_18_0)
    expr5 = msat_make_plus(menv, xs[11], n_10_0)
    expr6 = msat_make_plus(menv, xs[13], n_3_0)
    expr7 = msat_make_plus(menv, xs[16], n_14_0)
    expr8 = msat_make_plus(menv, xs[17], n_16_0)
    expr9 = msat_make_plus(menv, xs[19], n_7_0)
    expr10 = msat_make_plus(menv, xs[21], n_20_0)
    expr11 = msat_make_plus(menv, xs[23], n_14_0)
    expr12 = msat_make_plus(menv, xs[24], n_17_0)
    expr13 = msat_make_plus(menv, xs[28], n_20_0)
    expr14 = msat_make_plus(menv, xs[30], n_3_0)
    expr15 = msat_make_plus(menv, xs[31], n_3_0)
    expr16 = msat_make_plus(menv, xs[32], n_13_0)
    expr17 = msat_make_plus(menv, xs[33], n_12_0)
    _t = msat_make_and(menv,
                       msat_make_geq(menv, x_xs[29], expr0),
                       msat_make_geq(menv, x_xs[29], expr1),
                       msat_make_geq(menv, x_xs[29], expr2),
                       msat_make_geq(menv, x_xs[29], expr3),
                       msat_make_geq(menv, x_xs[29], expr4),
                       msat_make_geq(menv, x_xs[29], expr5),
                       msat_make_geq(menv, x_xs[29], expr6),
                       msat_make_geq(menv, x_xs[29], expr7),
                       msat_make_geq(menv, x_xs[29], expr8),
                       msat_make_geq(menv, x_xs[29], expr9),
                       msat_make_geq(menv, x_xs[29], expr10),
                       msat_make_geq(menv, x_xs[29], expr11),
                       msat_make_geq(menv, x_xs[29], expr12),
                       msat_make_geq(menv, x_xs[29], expr13),
                       msat_make_geq(menv, x_xs[29], expr14),
                       msat_make_geq(menv, x_xs[29], expr15),
                       msat_make_geq(menv, x_xs[29], expr16),
                       msat_make_geq(menv, x_xs[29], expr17),)
    _t = msat_make_and(menv, _t,
                       msat_make_or(menv,
                                    msat_make_equal(menv, x_xs[29], expr0),
                                    msat_make_equal(menv, x_xs[29], expr1),
                                    msat_make_equal(menv, x_xs[29], expr2),
                                    msat_make_equal(menv, x_xs[29], expr3),
                                    msat_make_equal(menv, x_xs[29], expr4),
                                    msat_make_equal(menv, x_xs[29], expr5),
                                    msat_make_equal(menv, x_xs[29], expr6),
                                    msat_make_equal(menv, x_xs[29], expr7),
                                    msat_make_equal(menv, x_xs[29], expr8),
                                    msat_make_equal(menv, x_xs[29], expr9),
                                    msat_make_equal(menv, x_xs[29], expr10),
                                    msat_make_equal(menv, x_xs[29], expr11),
                                    msat_make_equal(menv, x_xs[29], expr12),
                                    msat_make_equal(menv, x_xs[29], expr13),
                                    msat_make_equal(menv, x_xs[29], expr14),
                                    msat_make_equal(menv, x_xs[29], expr15),
                                    msat_make_equal(menv, x_xs[29], expr16),
                                    msat_make_equal(menv, x_xs[29], expr17),))
    trans = msat_make_and(menv, trans, _t)

    expr0 = msat_make_plus(menv, xs[0], n_4_0)
    expr1 = msat_make_plus(menv, xs[2], n_12_0)
    expr2 = msat_make_plus(menv, xs[3], n_10_0)
    expr3 = msat_make_plus(menv, xs[6], n_5_0)
    expr4 = msat_make_plus(menv, xs[7], n_8_0)
    expr5 = msat_make_plus(menv, xs[8], n_2_0)
    expr6 = msat_make_plus(menv, xs[9], n_16_0)
    expr7 = msat_make_plus(menv, xs[11], n_18_0)
    expr8 = msat_make_plus(menv, xs[13], n_13_0)
    expr9 = msat_make_plus(menv, xs[17], n_8_0)
    expr10 = msat_make_plus(menv, xs[18], n_10_0)
    expr11 = msat_make_plus(menv, xs[21], n_20_0)
    expr12 = msat_make_plus(menv, xs[22], n_3_0)
    expr13 = msat_make_plus(menv, xs[24], n_9_0)
    expr14 = msat_make_plus(menv, xs[28], n_20_0)
    expr15 = msat_make_plus(menv, xs[29], n_9_0)
    expr16 = msat_make_plus(menv, xs[33], n_12_0)
    expr17 = msat_make_plus(menv, xs[34], n_2_0)
    _t = msat_make_and(menv,
                       msat_make_geq(menv, x_xs[30], expr0),
                       msat_make_geq(menv, x_xs[30], expr1),
                       msat_make_geq(menv, x_xs[30], expr2),
                       msat_make_geq(menv, x_xs[30], expr3),
                       msat_make_geq(menv, x_xs[30], expr4),
                       msat_make_geq(menv, x_xs[30], expr5),
                       msat_make_geq(menv, x_xs[30], expr6),
                       msat_make_geq(menv, x_xs[30], expr7),
                       msat_make_geq(menv, x_xs[30], expr8),
                       msat_make_geq(menv, x_xs[30], expr9),
                       msat_make_geq(menv, x_xs[30], expr10),
                       msat_make_geq(menv, x_xs[30], expr11),
                       msat_make_geq(menv, x_xs[30], expr12),
                       msat_make_geq(menv, x_xs[30], expr13),
                       msat_make_geq(menv, x_xs[30], expr14),
                       msat_make_geq(menv, x_xs[30], expr15),
                       msat_make_geq(menv, x_xs[30], expr16),
                       msat_make_geq(menv, x_xs[30], expr17),)
    _t = msat_make_and(menv, _t,
                       msat_make_or(menv,
                                    msat_make_equal(menv, x_xs[30], expr0),
                                    msat_make_equal(menv, x_xs[30], expr1),
                                    msat_make_equal(menv, x_xs[30], expr2),
                                    msat_make_equal(menv, x_xs[30], expr3),
                                    msat_make_equal(menv, x_xs[30], expr4),
                                    msat_make_equal(menv, x_xs[30], expr5),
                                    msat_make_equal(menv, x_xs[30], expr6),
                                    msat_make_equal(menv, x_xs[30], expr7),
                                    msat_make_equal(menv, x_xs[30], expr8),
                                    msat_make_equal(menv, x_xs[30], expr9),
                                    msat_make_equal(menv, x_xs[30], expr10),
                                    msat_make_equal(menv, x_xs[30], expr11),
                                    msat_make_equal(menv, x_xs[30], expr12),
                                    msat_make_equal(menv, x_xs[30], expr13),
                                    msat_make_equal(menv, x_xs[30], expr14),
                                    msat_make_equal(menv, x_xs[30], expr15),
                                    msat_make_equal(menv, x_xs[30], expr16),
                                    msat_make_equal(menv, x_xs[30], expr17),))
    trans = msat_make_and(menv, trans, _t)

    expr0 = msat_make_plus(menv, xs[0], n_3_0)
    expr1 = msat_make_plus(menv, xs[1], n_11_0)
    expr2 = msat_make_plus(menv, xs[5], n_20_0)
    expr3 = msat_make_plus(menv, xs[6], n_12_0)
    expr4 = msat_make_plus(menv, xs[7], n_5_0)
    expr5 = msat_make_plus(menv, xs[9], n_16_0)
    expr6 = msat_make_plus(menv, xs[12], n_11_0)
    expr7 = msat_make_plus(menv, xs[14], n_4_0)
    expr8 = msat_make_plus(menv, xs[18], n_14_0)
    expr9 = msat_make_plus(menv, xs[19], n_20_0)
    expr10 = msat_make_plus(menv, xs[20], n_11_0)
    expr11 = msat_make_plus(menv, xs[22], n_5_0)
    expr12 = msat_make_plus(menv, xs[26], n_13_0)
    expr13 = msat_make_plus(menv, xs[27], n_20_0)
    expr14 = msat_make_plus(menv, xs[32], n_20_0)
    expr15 = msat_make_plus(menv, xs[33], n_8_0)
    expr16 = msat_make_plus(menv, xs[34], n_5_0)
    expr17 = msat_make_plus(menv, xs[35], n_20_0)
    _t = msat_make_and(menv,
                       msat_make_geq(menv, x_xs[31], expr0),
                       msat_make_geq(menv, x_xs[31], expr1),
                       msat_make_geq(menv, x_xs[31], expr2),
                       msat_make_geq(menv, x_xs[31], expr3),
                       msat_make_geq(menv, x_xs[31], expr4),
                       msat_make_geq(menv, x_xs[31], expr5),
                       msat_make_geq(menv, x_xs[31], expr6),
                       msat_make_geq(menv, x_xs[31], expr7),
                       msat_make_geq(menv, x_xs[31], expr8),
                       msat_make_geq(menv, x_xs[31], expr9),
                       msat_make_geq(menv, x_xs[31], expr10),
                       msat_make_geq(menv, x_xs[31], expr11),
                       msat_make_geq(menv, x_xs[31], expr12),
                       msat_make_geq(menv, x_xs[31], expr13),
                       msat_make_geq(menv, x_xs[31], expr14),
                       msat_make_geq(menv, x_xs[31], expr15),
                       msat_make_geq(menv, x_xs[31], expr16),
                       msat_make_geq(menv, x_xs[31], expr17),)
    _t = msat_make_and(menv, _t,
                       msat_make_or(menv,
                                    msat_make_equal(menv, x_xs[31], expr0),
                                    msat_make_equal(menv, x_xs[31], expr1),
                                    msat_make_equal(menv, x_xs[31], expr2),
                                    msat_make_equal(menv, x_xs[31], expr3),
                                    msat_make_equal(menv, x_xs[31], expr4),
                                    msat_make_equal(menv, x_xs[31], expr5),
                                    msat_make_equal(menv, x_xs[31], expr6),
                                    msat_make_equal(menv, x_xs[31], expr7),
                                    msat_make_equal(menv, x_xs[31], expr8),
                                    msat_make_equal(menv, x_xs[31], expr9),
                                    msat_make_equal(menv, x_xs[31], expr10),
                                    msat_make_equal(menv, x_xs[31], expr11),
                                    msat_make_equal(menv, x_xs[31], expr12),
                                    msat_make_equal(menv, x_xs[31], expr13),
                                    msat_make_equal(menv, x_xs[31], expr14),
                                    msat_make_equal(menv, x_xs[31], expr15),
                                    msat_make_equal(menv, x_xs[31], expr16),
                                    msat_make_equal(menv, x_xs[31], expr17),))
    trans = msat_make_and(menv, trans, _t)

    expr0 = msat_make_plus(menv, xs[1], n_16_0)
    expr1 = msat_make_plus(menv, xs[5], n_9_0)
    expr2 = msat_make_plus(menv, xs[9], n_12_0)
    expr3 = msat_make_plus(menv, xs[10], n_5_0)
    expr4 = msat_make_plus(menv, xs[12], n_16_0)
    expr5 = msat_make_plus(menv, xs[14], n_3_0)
    expr6 = msat_make_plus(menv, xs[17], n_13_0)
    expr7 = msat_make_plus(menv, xs[18], n_11_0)
    expr8 = msat_make_plus(menv, xs[20], n_7_0)
    expr9 = msat_make_plus(menv, xs[24], n_14_0)
    expr10 = msat_make_plus(menv, xs[25], n_20_0)
    expr11 = msat_make_plus(menv, xs[26], n_1_0)
    expr12 = msat_make_plus(menv, xs[27], n_14_0)
    expr13 = msat_make_plus(menv, xs[29], n_2_0)
    expr14 = msat_make_plus(menv, xs[30], n_2_0)
    expr15 = msat_make_plus(menv, xs[31], n_8_0)
    expr16 = msat_make_plus(menv, xs[32], n_9_0)
    expr17 = msat_make_plus(menv, xs[33], n_2_0)
    _t = msat_make_and(menv,
                       msat_make_geq(menv, x_xs[32], expr0),
                       msat_make_geq(menv, x_xs[32], expr1),
                       msat_make_geq(menv, x_xs[32], expr2),
                       msat_make_geq(menv, x_xs[32], expr3),
                       msat_make_geq(menv, x_xs[32], expr4),
                       msat_make_geq(menv, x_xs[32], expr5),
                       msat_make_geq(menv, x_xs[32], expr6),
                       msat_make_geq(menv, x_xs[32], expr7),
                       msat_make_geq(menv, x_xs[32], expr8),
                       msat_make_geq(menv, x_xs[32], expr9),
                       msat_make_geq(menv, x_xs[32], expr10),
                       msat_make_geq(menv, x_xs[32], expr11),
                       msat_make_geq(menv, x_xs[32], expr12),
                       msat_make_geq(menv, x_xs[32], expr13),
                       msat_make_geq(menv, x_xs[32], expr14),
                       msat_make_geq(menv, x_xs[32], expr15),
                       msat_make_geq(menv, x_xs[32], expr16),
                       msat_make_geq(menv, x_xs[32], expr17),)
    _t = msat_make_and(menv, _t,
                       msat_make_or(menv,
                                    msat_make_equal(menv, x_xs[32], expr0),
                                    msat_make_equal(menv, x_xs[32], expr1),
                                    msat_make_equal(menv, x_xs[32], expr2),
                                    msat_make_equal(menv, x_xs[32], expr3),
                                    msat_make_equal(menv, x_xs[32], expr4),
                                    msat_make_equal(menv, x_xs[32], expr5),
                                    msat_make_equal(menv, x_xs[32], expr6),
                                    msat_make_equal(menv, x_xs[32], expr7),
                                    msat_make_equal(menv, x_xs[32], expr8),
                                    msat_make_equal(menv, x_xs[32], expr9),
                                    msat_make_equal(menv, x_xs[32], expr10),
                                    msat_make_equal(menv, x_xs[32], expr11),
                                    msat_make_equal(menv, x_xs[32], expr12),
                                    msat_make_equal(menv, x_xs[32], expr13),
                                    msat_make_equal(menv, x_xs[32], expr14),
                                    msat_make_equal(menv, x_xs[32], expr15),
                                    msat_make_equal(menv, x_xs[32], expr16),
                                    msat_make_equal(menv, x_xs[32], expr17),))
    trans = msat_make_and(menv, trans, _t)

    expr0 = msat_make_plus(menv, xs[0], n_14_0)
    expr1 = msat_make_plus(menv, xs[2], n_11_0)
    expr2 = msat_make_plus(menv, xs[4], n_7_0)
    expr3 = msat_make_plus(menv, xs[5], n_1_0)
    expr4 = msat_make_plus(menv, xs[6], n_20_0)
    expr5 = msat_make_plus(menv, xs[7], n_12_0)
    expr6 = msat_make_plus(menv, xs[8], n_5_0)
    expr7 = msat_make_plus(menv, xs[11], n_4_0)
    expr8 = msat_make_plus(menv, xs[14], n_18_0)
    expr9 = msat_make_plus(menv, xs[15], n_1_0)
    expr10 = msat_make_plus(menv, xs[19], n_18_0)
    expr11 = msat_make_plus(menv, xs[20], n_20_0)
    expr12 = msat_make_plus(menv, xs[24], n_3_0)
    expr13 = msat_make_plus(menv, xs[25], n_11_0)
    expr14 = msat_make_plus(menv, xs[27], n_11_0)
    expr15 = msat_make_plus(menv, xs[32], n_17_0)
    expr16 = msat_make_plus(menv, xs[34], n_20_0)
    expr17 = msat_make_plus(menv, xs[35], n_7_0)
    _t = msat_make_and(menv,
                       msat_make_geq(menv, x_xs[33], expr0),
                       msat_make_geq(menv, x_xs[33], expr1),
                       msat_make_geq(menv, x_xs[33], expr2),
                       msat_make_geq(menv, x_xs[33], expr3),
                       msat_make_geq(menv, x_xs[33], expr4),
                       msat_make_geq(menv, x_xs[33], expr5),
                       msat_make_geq(menv, x_xs[33], expr6),
                       msat_make_geq(menv, x_xs[33], expr7),
                       msat_make_geq(menv, x_xs[33], expr8),
                       msat_make_geq(menv, x_xs[33], expr9),
                       msat_make_geq(menv, x_xs[33], expr10),
                       msat_make_geq(menv, x_xs[33], expr11),
                       msat_make_geq(menv, x_xs[33], expr12),
                       msat_make_geq(menv, x_xs[33], expr13),
                       msat_make_geq(menv, x_xs[33], expr14),
                       msat_make_geq(menv, x_xs[33], expr15),
                       msat_make_geq(menv, x_xs[33], expr16),
                       msat_make_geq(menv, x_xs[33], expr17),)
    _t = msat_make_and(menv, _t,
                       msat_make_or(menv,
                                    msat_make_equal(menv, x_xs[33], expr0),
                                    msat_make_equal(menv, x_xs[33], expr1),
                                    msat_make_equal(menv, x_xs[33], expr2),
                                    msat_make_equal(menv, x_xs[33], expr3),
                                    msat_make_equal(menv, x_xs[33], expr4),
                                    msat_make_equal(menv, x_xs[33], expr5),
                                    msat_make_equal(menv, x_xs[33], expr6),
                                    msat_make_equal(menv, x_xs[33], expr7),
                                    msat_make_equal(menv, x_xs[33], expr8),
                                    msat_make_equal(menv, x_xs[33], expr9),
                                    msat_make_equal(menv, x_xs[33], expr10),
                                    msat_make_equal(menv, x_xs[33], expr11),
                                    msat_make_equal(menv, x_xs[33], expr12),
                                    msat_make_equal(menv, x_xs[33], expr13),
                                    msat_make_equal(menv, x_xs[33], expr14),
                                    msat_make_equal(menv, x_xs[33], expr15),
                                    msat_make_equal(menv, x_xs[33], expr16),
                                    msat_make_equal(menv, x_xs[33], expr17),))
    trans = msat_make_and(menv, trans, _t)

    expr0 = msat_make_plus(menv, xs[3], n_8_0)
    expr1 = msat_make_plus(menv, xs[4], n_16_0)
    expr2 = msat_make_plus(menv, xs[5], n_12_0)
    expr3 = msat_make_plus(menv, xs[6], n_5_0)
    expr4 = msat_make_plus(menv, xs[7], n_18_0)
    expr5 = msat_make_plus(menv, xs[10], n_14_0)
    expr6 = msat_make_plus(menv, xs[11], n_14_0)
    expr7 = msat_make_plus(menv, xs[12], n_16_0)
    expr8 = msat_make_plus(menv, xs[14], n_1_0)
    expr9 = msat_make_plus(menv, xs[16], n_7_0)
    expr10 = msat_make_plus(menv, xs[17], n_20_0)
    expr11 = msat_make_plus(menv, xs[21], n_3_0)
    expr12 = msat_make_plus(menv, xs[22], n_9_0)
    expr13 = msat_make_plus(menv, xs[23], n_2_0)
    expr14 = msat_make_plus(menv, xs[25], n_18_0)
    expr15 = msat_make_plus(menv, xs[26], n_8_0)
    expr16 = msat_make_plus(menv, xs[29], n_7_0)
    expr17 = msat_make_plus(menv, xs[31], n_12_0)
    _t = msat_make_and(menv,
                       msat_make_geq(menv, x_xs[34], expr0),
                       msat_make_geq(menv, x_xs[34], expr1),
                       msat_make_geq(menv, x_xs[34], expr2),
                       msat_make_geq(menv, x_xs[34], expr3),
                       msat_make_geq(menv, x_xs[34], expr4),
                       msat_make_geq(menv, x_xs[34], expr5),
                       msat_make_geq(menv, x_xs[34], expr6),
                       msat_make_geq(menv, x_xs[34], expr7),
                       msat_make_geq(menv, x_xs[34], expr8),
                       msat_make_geq(menv, x_xs[34], expr9),
                       msat_make_geq(menv, x_xs[34], expr10),
                       msat_make_geq(menv, x_xs[34], expr11),
                       msat_make_geq(menv, x_xs[34], expr12),
                       msat_make_geq(menv, x_xs[34], expr13),
                       msat_make_geq(menv, x_xs[34], expr14),
                       msat_make_geq(menv, x_xs[34], expr15),
                       msat_make_geq(menv, x_xs[34], expr16),
                       msat_make_geq(menv, x_xs[34], expr17),)
    _t = msat_make_and(menv, _t,
                       msat_make_or(menv,
                                    msat_make_equal(menv, x_xs[34], expr0),
                                    msat_make_equal(menv, x_xs[34], expr1),
                                    msat_make_equal(menv, x_xs[34], expr2),
                                    msat_make_equal(menv, x_xs[34], expr3),
                                    msat_make_equal(menv, x_xs[34], expr4),
                                    msat_make_equal(menv, x_xs[34], expr5),
                                    msat_make_equal(menv, x_xs[34], expr6),
                                    msat_make_equal(menv, x_xs[34], expr7),
                                    msat_make_equal(menv, x_xs[34], expr8),
                                    msat_make_equal(menv, x_xs[34], expr9),
                                    msat_make_equal(menv, x_xs[34], expr10),
                                    msat_make_equal(menv, x_xs[34], expr11),
                                    msat_make_equal(menv, x_xs[34], expr12),
                                    msat_make_equal(menv, x_xs[34], expr13),
                                    msat_make_equal(menv, x_xs[34], expr14),
                                    msat_make_equal(menv, x_xs[34], expr15),
                                    msat_make_equal(menv, x_xs[34], expr16),
                                    msat_make_equal(menv, x_xs[34], expr17),))
    trans = msat_make_and(menv, trans, _t)

    expr0 = msat_make_plus(menv, xs[4], n_5_0)
    expr1 = msat_make_plus(menv, xs[6], n_9_0)
    expr2 = msat_make_plus(menv, xs[7], n_3_0)
    expr3 = msat_make_plus(menv, xs[8], n_2_0)
    expr4 = msat_make_plus(menv, xs[10], n_9_0)
    expr5 = msat_make_plus(menv, xs[11], n_8_0)
    expr6 = msat_make_plus(menv, xs[14], n_6_0)
    expr7 = msat_make_plus(menv, xs[15], n_6_0)
    expr8 = msat_make_plus(menv, xs[16], n_14_0)
    expr9 = msat_make_plus(menv, xs[17], n_6_0)
    expr10 = msat_make_plus(menv, xs[18], n_20_0)
    expr11 = msat_make_plus(menv, xs[19], n_9_0)
    expr12 = msat_make_plus(menv, xs[22], n_2_0)
    expr13 = msat_make_plus(menv, xs[24], n_5_0)
    expr14 = msat_make_plus(menv, xs[25], n_6_0)
    expr15 = msat_make_plus(menv, xs[27], n_9_0)
    expr16 = msat_make_plus(menv, xs[29], n_5_0)
    expr17 = msat_make_plus(menv, xs[32], n_18_0)
    _t = msat_make_and(menv,
                       msat_make_geq(menv, x_xs[35], expr0),
                       msat_make_geq(menv, x_xs[35], expr1),
                       msat_make_geq(menv, x_xs[35], expr2),
                       msat_make_geq(menv, x_xs[35], expr3),
                       msat_make_geq(menv, x_xs[35], expr4),
                       msat_make_geq(menv, x_xs[35], expr5),
                       msat_make_geq(menv, x_xs[35], expr6),
                       msat_make_geq(menv, x_xs[35], expr7),
                       msat_make_geq(menv, x_xs[35], expr8),
                       msat_make_geq(menv, x_xs[35], expr9),
                       msat_make_geq(menv, x_xs[35], expr10),
                       msat_make_geq(menv, x_xs[35], expr11),
                       msat_make_geq(menv, x_xs[35], expr12),
                       msat_make_geq(menv, x_xs[35], expr13),
                       msat_make_geq(menv, x_xs[35], expr14),
                       msat_make_geq(menv, x_xs[35], expr15),
                       msat_make_geq(menv, x_xs[35], expr16),
                       msat_make_geq(menv, x_xs[35], expr17),)
    _t = msat_make_and(menv, _t,
                       msat_make_or(menv,
                                    msat_make_equal(menv, x_xs[35], expr0),
                                    msat_make_equal(menv, x_xs[35], expr1),
                                    msat_make_equal(menv, x_xs[35], expr2),
                                    msat_make_equal(menv, x_xs[35], expr3),
                                    msat_make_equal(menv, x_xs[35], expr4),
                                    msat_make_equal(menv, x_xs[35], expr5),
                                    msat_make_equal(menv, x_xs[35], expr6),
                                    msat_make_equal(menv, x_xs[35], expr7),
                                    msat_make_equal(menv, x_xs[35], expr8),
                                    msat_make_equal(menv, x_xs[35], expr9),
                                    msat_make_equal(menv, x_xs[35], expr10),
                                    msat_make_equal(menv, x_xs[35], expr11),
                                    msat_make_equal(menv, x_xs[35], expr12),
                                    msat_make_equal(menv, x_xs[35], expr13),
                                    msat_make_equal(menv, x_xs[35], expr14),
                                    msat_make_equal(menv, x_xs[35], expr15),
                                    msat_make_equal(menv, x_xs[35], expr16),
                                    msat_make_equal(menv, x_xs[35], expr17),))
    trans = msat_make_and(menv, trans, _t)

    # ltl property: ((x_34 - x_14 >= 6) | ((x_25 - x_17 > -13) & (x_9 - x_32 >= 5)))
    ltl = msat_make_or(menv, msat_make_geq(menv, msat_make_minus(menv, xs[34], xs[14]), msat_make_number(menv, "6")), msat_make_and(menv, msat_make_gt(menv, msat_make_minus(menv, xs[25], xs[17]), msat_make_number(menv, "-13")), msat_make_geq(menv, msat_make_minus(menv, xs[9], xs[32]), msat_make_number(menv, "5"))))

    return TermMap(curr2next), init, trans, ltl
