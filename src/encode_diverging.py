from typing import Tuple, Dict
from mathsat import (msat_term, msat_env,
                     msat_get_rational_type,
                     msat_declare_function, msat_make_constant,
                     msat_make_and, msat_make_or, msat_make_not,
                     msat_make_equal, msat_make_leq,
                     msat_make_number,
                     msat_make_plus,
                     msat_term_repr)

from utils import name_next


def msat_make_impl(menv: msat_env,
                   arg0: msat_term, arg1: msat_term) -> msat_term:
    n_arg0 = msat_make_not(menv, arg0)
    return msat_make_or(menv, n_arg0, arg1)


def encode_diverging(menv, enc, div_s, symbs=None, init=None, trans=None,
                     ltl=None) -> Tuple[Dict[msat_term, msat_term],
                                        msat_term, msat_term, msat_term]:
    if symbs is None:
        symbs = {}
    monitor_name = "_diverge_{}".format(msat_term_repr(div_s))
    real_type = msat_get_rational_type(menv)
    monitor = msat_declare_function(menv, monitor_name, real_type)
    monitor = msat_make_constant(menv, monitor)
    x_monitor = msat_declare_function(menv, name_next(monitor_name),
                                      real_type)
    x_monitor = msat_make_constant(menv, x_monitor)

    one = msat_make_number(menv, "1")
    # monitor = div_s
    init = msat_make_equal(menv, monitor, div_s) if init is None \
        else msat_make_and(menv, init,
                           msat_make_equal(menv, monitor, div_s))

    # 1 <= monitor -> monitor' = div_s
    monitor_geq_1 = msat_make_leq(menv, one, monitor)
    curr_impl = msat_make_impl(menv,
                               monitor_geq_1,
                               msat_make_equal(menv, x_monitor, div_s))
    # 1 > monitor -> monitor' = monitor + div_s
    curr_impl = msat_make_and(
        menv, curr_impl,
        msat_make_impl(menv, msat_make_not(menv, monitor_geq_1),
                       msat_make_equal(menv, x_monitor,
                                       msat_make_plus(menv, monitor, div_s))))
    trans = curr_impl if trans is None \
        else msat_make_and(menv, trans, curr_impl)
    # G F monitor >= 1
    lhs = enc.make_G(enc.make_F(monitor_geq_1))
    ltl = lhs if ltl is None else msat_make_impl(menv, lhs, ltl)

    symbs[monitor] = x_monitor
    return symbs, init, trans, ltl
