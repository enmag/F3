from collections import Iterable
from itertools import combinations
from math import log, ceil

from mathsat import msat_term, msat_env
from mathsat import msat_make_constant, msat_declare_function
from mathsat import msat_get_rational_type, msat_get_bool_type
from mathsat import msat_make_and, msat_make_not, msat_make_or, msat_make_iff
from mathsat import msat_make_leq, msat_make_equal, msat_make_true
from mathsat import msat_make_number, msat_make_plus, msat_make_times

from ltl.ltl import TermMap, LTLEncoder
from utils import name_next

num_procs = 24
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


def check_ltl(menv: msat_env, enc: LTLEncoder) -> (Iterable, msat_term,
                                                   msat_term, msat_term):
    assert menv
    assert isinstance(menv, msat_env)
    assert enc
    assert isinstance(enc, LTLEncoder)
    real_type = msat_get_rational_type(menv)

    delta, x_delta = decl_consts(menv, delta_name, real_type)
    transm_time, x_transm_time = decl_consts(menv, "tot_transm_time",
                                             real_type)

    curr2next = {delta: x_delta, transm_time: x_transm_time}

    mgr = TokenManager("mgr", menv, enc, delta)
    stations = [Station("st{}".format(i), menv, enc, mgr, delta)
                for i in range(num_procs)]
    for s, x_s in mgr.symb2next.items():
        curr2next[s] = x_s
    for comp in stations:
        for s, x_s in comp.symb2next.items():
            assert s not in curr2next.keys()
            curr2next[s] = x_s

    zero = msat_make_number(menv, "0")

    # init: tot_transm_time = 0
    init = msat_make_equal(menv, transm_time, zero)

    # invar: delta >= 0
    init = msat_make_and(menv, init, msat_make_geq(menv, delta, zero))
    trans = msat_make_geq(menv, x_delta, zero)

    # only 1 station moves
    for s0, s1 in combinations(stations, 2):
        trans = msat_make_and(menv, trans,
                              msat_make_or(menv, s0.stutter, s1.stutter))
    # sync stations and mgr
    st_acquire = stations[0].acquire
    for st in stations[1:]:
        st_acquire = msat_make_or(menv, st_acquire, st.acquire)
    trans = msat_make_and(menv, trans,
                          msat_make_iff(menv, mgr.acquire, st_acquire))
    st_release = stations[0].release
    for st in stations[1:]:
        st_release = msat_make_or(menv, st_release, st.release)
    trans = msat_make_and(menv, trans,
                          msat_make_iff(menv, mgr.release, st_release))
    # (mgr.counting & mgr.idle') -> total_transm_time' = total_transm_time + mgr.c
    lhs = msat_make_and(menv, mgr.counting, mgr.x_idle)
    rhs = msat_make_equal(menv, x_transm_time,
                          msat_make_plus(menv, transm_time, mgr.c))
    trans = msat_make_and(menv, trans,
                          msat_make_impl(menv, lhs, rhs))
    # !(mgr.counting & mgr.idle') -> total_transm_time' = total_transm_time
    lhs = msat_make_not(menv, lhs)
    rhs = msat_make_equal(menv, x_transm_time, transm_time)
    trans = msat_make_and(menv, trans,
                          msat_make_impl(menv, lhs, rhs))

    init = msat_make_and(menv, init, mgr.init)
    trans = msat_make_and(menv, trans, mgr.trans)
    for s in stations:
        init = msat_make_and(menv, init, s.init)
        trans = msat_make_and(menv, trans, s.trans)

    # (G F (mgr.counting & mgr.idle')) -> G F total_transm_time < 10
    lhs = enc.make_G(enc.make_F(msat_make_and(menv, mgr.counting,
                                              enc.make_X(mgr.idle))))
    rhs = msat_make_lt(menv, transm_time, msat_make_number(menv, "10"))
    rhs = enc.make_G(enc.make_F(rhs))
    ltl = msat_make_impl(menv, lhs, rhs)
    return TermMap(curr2next), init, trans, ltl


class Module:
    """Synchronous component"""
    def __init__(self, name: str, menv: msat_env, enc: LTLEncoder,
                 *args, **kwargs):
        self.name = name
        self.menv = menv
        self.enc = enc
        self.symb2next = {}
        true = msat_make_true(menv)
        self.init = true
        self.trans = true

    def _symb(self, v_name, v_type):
        v_name = "{}_{}".format(self.name, v_name)
        return decl_consts(self.menv, v_name, v_type)

    def _enum(self, v_name: str, enum_size: int):
        bool_type = msat_get_bool_type(self.menv)
        num_bits = ceil(log(enum_size, 2))
        b_vars = []
        for idx in range(num_bits):
            c_name = "{}{}".format(v_name, idx)
            b_vars.append(tuple(self._symb(c_name, bool_type)))
        vals = []
        x_vals = []
        for enum_val in range(enum_size):
            bit_val = format(enum_val, '0{}b'.format(num_bits))
            assert len(bit_val) == num_bits
            assert all(c in {'0', '1'} for c in bit_val)
            assign = [b_vars[idx] if c == '1' else
                      (msat_make_not(self.menv, b_vars[idx][0]),
                       msat_make_not(self.menv, b_vars[idx][1]))
                      for idx, c in enumerate(reversed(bit_val))]
            pred = assign[0][0]
            x_pred = assign[0][1]
            for it in assign[1:]:
                pred = msat_make_and(self.menv, pred, it[0])
                x_pred = msat_make_and(self.menv, x_pred, it[1])
            vals.append(pred)
            x_vals.append(x_pred)
        assert len(vals) == enum_size
        assert len(x_vals) == enum_size
        return b_vars, vals, x_vals


class TokenManager(Module):
    """TokenManager module"""
    def __init__(self, name: str, menv: msat_env, enc: LTLEncoder, delta):
        super().__init__(name, menv, enc)

        real_type = msat_get_rational_type(menv)
        bool_type = msat_get_bool_type(menv)
        loc, x_loc = self._symb("l", bool_type)
        evt_symbs, evts, x_evts = self._enum("evt", 3)
        c, x_c = self._symb("c", real_type)
        timeout, x_timeout = self._symb("timeout", real_type)

        self.timeout = timeout
        self.x_timeout = x_timeout
        self.c = c

        self.idle = loc
        self.counting = msat_make_not(menv, loc)
        self.x_idle = x_loc
        self.x_counting = msat_make_not(menv, x_loc)
        self.acquire = evts[0]
        self.release = evts[1]
        self.stutter = evts[2]

        self.symb2next = {loc: x_loc, c: x_c, timeout: x_timeout}
        for s, x_s in evt_symbs:
            assert s not in self.symb2next
            self.symb2next[s] = x_s

        zero = msat_make_number(menv, "0")

        # bound evt
        bound_evt = evts[0]
        x_bound_evt = x_evts[0]
        for evt, x_evt in zip(evts[1:], x_evts[1:]):
            bound_evt = msat_make_or(menv, bound_evt, evt)
            x_bound_evt = msat_make_or(menv, x_bound_evt, x_evt)
        self.init = bound_evt
        self.trans = x_bound_evt

        # idle & c = 0 & timeout = 0
        self.init = msat_make_and(
            menv,
            msat_make_and(menv, self.init, self.idle),
            msat_make_and(menv,
                          msat_make_equal(menv, c, zero),
                          msat_make_equal(menv, timeout, zero)))

        # invar: counting -> c <= timeout
        rhs = msat_make_leq(menv, c, timeout)
        self.init = msat_make_and(menv, self.init,
                                  msat_make_impl(menv, self.counting, rhs))
        rhs = msat_make_leq(menv, x_c, x_timeout)
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, self.x_counting, rhs))

        # (delta > 0 | stutter) -> c' = c + delta & l' = l & timeout' = timeout
        lhs = msat_make_or(menv, self.stutter,
                           msat_make_gt(menv, delta, zero))
        rhs = msat_make_and(
            menv,
            msat_make_and(menv, msat_make_iff(menv, x_loc, loc),
                          msat_make_equal(menv, x_c,
                                          msat_make_plus(menv, c, delta))),
            msat_make_equal(menv, x_timeout, timeout))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))

        disc_t = msat_make_and(menv, msat_make_equal(menv, delta, zero),
                               msat_make_or(menv, self.acquire, self.release))
        # (idle) -> (acquire & counting' & c' = 0)
        lhs = msat_make_and(menv, disc_t, self.idle)
        rhs = msat_make_and(menv, self.acquire,
                            msat_make_and(menv, self.x_counting,
                                          msat_make_equal(menv, x_c, zero)))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        # (counting) -> (release & idle' & c' = 0 & timeout' = 0)
        lhs = msat_make_and(menv, disc_t, self.counting)
        rhs = msat_make_and(
            menv,
            msat_make_and(menv, self.x_idle, self.release),
            msat_make_and(menv,
                          msat_make_equal(menv, x_c, zero),
                          msat_make_equal(menv, x_timeout, zero)))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))


class Station(Module):
    """Station module"""
    def __init__(self, name: str, menv: msat_env, enc: LTLEncoder, mgr, delta):
        super().__init__(name, menv, enc)

        real_type = msat_get_rational_type(menv)
        bool_type = msat_get_bool_type(menv)
        loc, x_loc = self._symb("l", bool_type)
        evt_symbs, evts, x_evts = self._enum("evt", 3)
        req_time, x_req_time = self._symb("req_time", real_type)

        self.idle = loc
        self.transm = msat_make_not(menv, loc)
        self.x_idle = x_loc
        self.x_transm = msat_make_not(menv, x_loc)
        self.acquire = evts[0]
        self.release = evts[1]
        self.stutter = evts[2]

        self.symb2next = {loc: x_loc, req_time: x_req_time}
        for s, x_s in evt_symbs:
            assert s not in self.symb2next
            self.symb2next[s] = x_s

        zero = msat_make_number(menv, "0")

        # bound evt
        bound_evt = evts[0]
        x_bound_evt = x_evts[0]
        for evt, x_evt in zip(evts[1:], x_evts[1:]):
            bound_evt = msat_make_or(menv, bound_evt, evt)
            x_bound_evt = msat_make_or(menv, x_bound_evt, x_evt)
        self.init = bound_evt
        self.trans = x_bound_evt

        # idle
        self.init = msat_make_and(menv, self.init, self.idle)

        # invar: req_time > 0
        self.init = msat_make_and(menv, self.init,
                                  msat_make_gt(menv, req_time, zero))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_gt(menv, x_req_time, zero))

        # (delta > 0 | stutter) -> l' = l & req_time' = req_time
        lhs = msat_make_or(menv, self.stutter,
                           msat_make_gt(menv, delta, zero))
        rhs = msat_make_and(
            menv,
            msat_make_iff(menv, x_loc, loc),
            msat_make_equal(menv, x_req_time, req_time))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))

        disc_t = msat_make_and(menv, msat_make_equal(menv, delta, zero),
                               msat_make_or(menv, self.acquire, self.release))
        # (idle) -> (acquire & transm' & mgr.timeout' = req_time & req_time' = req_time)
        lhs = msat_make_and(menv, disc_t, self.idle)
        rhs = msat_make_and(
            menv,
            msat_make_and(menv, self.acquire, self.x_transm),
            msat_make_and(menv,
                          msat_make_equal(menv, mgr.x_timeout, req_time),
                          msat_make_equal(menv, x_req_time, req_time)))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        # (transm) -> (release & mgr.c > 0 & idle')
        lhs = msat_make_and(menv, disc_t, self.transm)
        rhs = msat_make_and(
            menv, self.release,
            msat_make_and(menv, msat_make_gt(menv, mgr.c, zero), self.x_idle))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
