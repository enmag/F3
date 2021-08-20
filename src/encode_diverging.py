from typing import Tuple, Dict
from mathsat import (msat_term, msat_env,
                     msat_get_rational_type,
                     msat_declare_function, msat_make_constant,
                     msat_make_and, msat_make_or, msat_make_not,
                     msat_make_equal, msat_make_leq,
                     msat_make_number, msat_make_plus, msat_term_repr)

from utils import name_next

_DET_DIV_MONITOR = True

def get_div_mode() -> bool:
    global _DET_DIV_MONITOR
    return _DET_DIV_MONITOR


def set_div_mode(val: bool) -> None:
    global _DET_DIV_MONITOR
    assert isinstance(val, bool)
    _DET_DIV_MONITOR = val


def msat_make_impl(menv: msat_env,
                   arg0: msat_term, arg1: msat_term) -> msat_term:
    n_arg0 = msat_make_not(menv, arg0)
    return msat_make_or(menv, n_arg0, arg1)


def msat_make_lt(menv: msat_env, arg0: msat_term, arg1: msat_term):
    geq = msat_make_leq(menv, arg1, arg0)
    return msat_make_not(menv, geq)


def encode_diverging(menv, enc, div_s, symbs, init, trans,
                     ltl) -> Tuple[Dict[msat_term, msat_term],
                                   msat_term, msat_term, msat_term]:
    assert symbs is not None
    monitor_name = f"_diverge_{msat_term_repr(div_s)}"
    real_type = msat_get_rational_type(menv)
    monitor = msat_make_constant(menv, msat_declare_function(menv, monitor_name,
                                                             real_type))
    x_monitor = msat_make_constant(menv,
                                   msat_declare_function(menv,
                                                         name_next(monitor_name),
                                                         real_type))
    symbs[monitor] = x_monitor
    one = msat_make_number(menv, "1")
    if get_div_mode() is True:
        # monitor = div_s
        m_init = msat_make_equal(menv, monitor, div_s)
        monitor_geq_1 = msat_make_leq(menv, one, monitor)
        # (1 <= monitor -> monitor' = div_s) &
        # (1 > monitor -> monitor' = monitor + div_s)
        m_trans = msat_make_and(
            menv,
            msat_make_impl(menv, monitor_geq_1,
                           msat_make_equal(menv, x_monitor, div_s)),
            msat_make_impl(menv, msat_make_not(menv, monitor_geq_1),
                           msat_make_equal(menv, x_monitor,
                                           msat_make_plus(menv, monitor,
                                                          div_s))))
        # G F monitor >= 1
        m_ltl = enc.make_G(enc.make_F(monitor_geq_1))
    else:
        zero = msat_make_number(menv, "0")
        # monitor = 0
        m_init = msat_make_equal(menv, monitor, zero)
        # monitor' = monitor + div_s | (1 < monitor & monitor' = 0)
        m_trans = msat_make_or(
            menv,
            msat_make_equal(menv, x_monitor,
                            msat_make_plus(menv, monitor, div_s)),
            msat_make_and(menv,
                          msat_make_lt(menv, one, monitor),
                          msat_make_equal(menv, x_monitor, zero)))

        # G F monitor = 0 & 0 < div_s
        m_ltl = enc.make_G(enc.make_F(msat_make_and(menv, m_init,
                                                    msat_make_lt(menv, zero,
                                                                 div_s))))

    return (symbs,
            msat_make_and(menv, init, m_init),
            msat_make_and(menv, trans, m_trans),
            msat_make_impl(menv, m_ltl, ltl))
