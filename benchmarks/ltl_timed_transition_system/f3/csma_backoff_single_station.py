from collections import Iterable
from itertools import chain
from math import log, ceil

from mathsat import msat_term, msat_env
from mathsat import msat_make_constant, msat_declare_function
from mathsat import msat_get_rational_type, msat_get_bool_type
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
    real_type = msat_get_rational_type(menv)

    LAMBDA = msat_make_number(menv, "404")
    SIGMA = msat_make_number(menv, "13")

    delta, x_delta = decl_consts(menv, delta_name, real_type)

    curr2next = {delta: x_delta}

    bus = Bus("bus", menv, enc, SIGMA, delta, x_delta)
    station = Station("st", menv, enc, LAMBDA, SIGMA, delta)
    env = Environment("env", menv, enc)

    components = [bus, station, env]
    for comp in components:
        for s, x_s in comp.symb2next.items():
            assert s not in curr2next.keys()
            curr2next[s] = x_s

    zero = msat_make_number(menv, "0")
    # invar: delta >= 0
    init = msat_make_geq(menv, delta, zero)
    trans = msat_make_geq(menv, x_delta, zero)

    for comp in components:
        init = msat_make_and(menv, init, comp.init)
        trans = msat_make_and(menv, trans, comp.trans)

    d_eq_0 = msat_make_equal(menv, delta, zero)

    # station and env do not move together.
    trans = msat_make_and(menv, trans,
                          msat_make_or(menv, env.evt_stutter,
                                       station.evt_stutter))
    # not all stutter
    not_all_stutter = msat_make_or(
        menv,
        msat_make_not(menv, bus.evt_stutter),
        msat_make_or(menv,
                     msat_make_not(menv, env.evt_stutter),
                     msat_make_not(menv, station.evt_stutter)))
    trans = msat_make_and(menv, trans,
                          msat_make_impl(menv, d_eq_0, not_all_stutter))

    # sync on evt_begin
    sync = msat_make_iff(menv, bus.evt_begin,
                         msat_make_or(menv, station.evt_begin,
                                      env.evt_begin))
    trans = msat_make_and(menv, trans,
                          msat_make_impl(menv, d_eq_0, sync))
    # sync evt_end
    sync = msat_make_iff(menv, bus.evt_end,
                         msat_make_or(menv, station.evt_end,
                                      env.evt_end))
    trans = msat_make_and(menv, trans,
                          msat_make_impl(menv, d_eq_0, sync))

    # sync on evt_busy
    sync = msat_make_iff(menv, bus.evt_busy,
                         msat_make_or(menv, station.evt_busy,
                                      env.evt_busy))
    trans = msat_make_and(menv, trans,
                          msat_make_impl(menv, d_eq_0, sync))
    # sync bus on evt_cd
    sync = msat_make_iff(menv, bus.evt_cd,
                         msat_make_or(menv, station.evt_cd,
                                      env.evt_cd))
    trans = msat_make_and(menv, trans,
                          msat_make_impl(menv, d_eq_0, sync))
    # station.cd <-> bus.evt_cd & bus.cd_id
    sync = msat_make_iff(menv, station.evt_cd,
                         msat_make_and(menv, bus.evt_cd, bus.cd_id))
    trans = msat_make_and(menv, trans, msat_make_impl(menv, d_eq_0, sync))
    # env.cd <-> bus.evt_cd & !bus.cd_id
    sync = msat_make_iff(menv, env.evt_cd,
                         msat_make_and(menv, bus.evt_cd,
                                       msat_make_not(menv, bus.cd_id)))
    trans = msat_make_and(menv, trans, msat_make_impl(menv, d_eq_0, sync))

    # (G F s0.transm) -> (G F s0.wait)
    lhs = enc.make_G(enc.make_F(station.transm))
    rhs = enc.make_G(enc.make_F(station.wait))
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
                      for idx, c in enumerate(bit_val)]
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


class Environment(Module):
    """Environment module"""
    def __init__(self, name: str, menv: msat_env, enc: LTLEncoder):
        super().__init__(name, menv, enc)

        evt_symbs, evts, x_evts = self._enum("evt", 5)
        self.symb2next = {}
        for s, x_s in evt_symbs:
            self.symb2next[s] = x_s

        self.evt_stutter = evts[0]
        self.evt_begin = evts[1]
        self.evt_end = evts[2]
        self.evt_busy = evts[3]
        self.evt_cd = evts[4]

        x_evt_stutter = x_evts[0]
        x_evt_begin = x_evts[1]
        x_evt_end = x_evts[2]
        x_evt_busy = x_evts[3]
        x_evt_cd = x_evts[4]

        # bound evt
        self.init = msat_make_or(
            menv,
            msat_make_or(menv,
                         msat_make_or(menv, self.evt_stutter,
                                      self.evt_begin),
                         msat_make_or(menv, self.evt_end,
                                      self.evt_busy)),
            self.evt_cd)
        self.trans = msat_make_or(
            menv,
            msat_make_or(menv,
                         msat_make_or(menv, x_evt_stutter, x_evt_begin),
                         msat_make_or(menv, x_evt_end, x_evt_busy)),
            x_evt_cd)


class Station(Module):
    """Station module"""
    def __init__(self, name: str, menv: msat_env, enc: LTLEncoder,
                 LAMBDA, SIGMA, delta):
        super().__init__(name, menv, enc)

        real_type = msat_get_rational_type(menv)

        evt_symbs, evts, x_evts = self._enum("evt", 5)
        loc_symbs, locs, x_locs = self._enum("l", 3)
        x, x_x = self._symb("x", real_type)
        backoff, x_backoff = self._symb("backoff", real_type)
        self.backoff, self.x_backoff = backoff, x_backoff

        self.symb2next = {x: x_x, backoff: x_backoff}
        for s, x_s in evt_symbs:
            assert s not in self.symb2next
            self.symb2next[s] = x_s
        for s, x_s in loc_symbs:
            assert s not in self.symb2next
            self.symb2next[s] = x_s

        nums = [msat_make_number(menv, str(n))
                for n in range(5)]

        self.evt_stutter = evts[0]
        self.evt_begin = evts[1]
        self.evt_end = evts[2]
        self.evt_busy = evts[3]
        self.evt_cd = evts[4]

        x_evt_stutter = x_evts[0]
        x_evt_begin = x_evts[1]
        x_evt_end = x_evts[2]
        x_evt_busy = x_evts[3]
        x_evt_cd = x_evts[4]

        self.wait = locs[0]
        self.transm = locs[1]
        self.retry = locs[2]

        self.x_wait = x_locs[0]
        self.x_transm = x_locs[1]
        self.x_retry = x_locs[2]

        same_loc = msat_make_iff(menv, loc_symbs[0][1], loc_symbs[0][0])
        for s, x_s in loc_symbs[1:]:
            same_loc = msat_make_and(menv, same_loc,
                                     msat_make_iff(menv, x_s, s))

        # l = wait & x = 0 & backoff >= SIGMA
        self.init = msat_make_and(
            menv,
            msat_make_and(menv, self.wait,
                          msat_make_equal(menv, x, nums[0])),
            msat_make_geq(menv, backoff, SIGMA))
        # bound evt
        self.init = msat_make_and(
            menv, self.init,
            msat_make_or(menv,
                         msat_make_or(
                             menv,
                             msat_make_or(menv, self.evt_stutter,
                                          self.evt_begin),
                             msat_make_or(menv, self.evt_end,
                                          self.evt_busy)),
                         self.evt_cd))
        # bound l
        self.init = msat_make_and(
            menv, self.init,
            msat_make_or(menv,
                         self.wait,
                         msat_make_or(menv, self.transm, self.retry)))
        # invars
        self.init = msat_make_and(
            menv, self.init,
            msat_make_impl(menv, self.transm, msat_make_leq(menv, x, LAMBDA)))

        # bound evt
        self.trans = msat_make_and(
            menv, self.trans,
            msat_make_or(menv,
                         msat_make_or(
                             menv,
                             msat_make_or(menv, x_evt_stutter,
                                          x_evt_begin),
                             msat_make_or(menv, x_evt_end,
                                          x_evt_busy)),
                         x_evt_cd))
        # bound l
        self.trans = msat_make_and(
            menv, self.trans,
            msat_make_or(menv, self.x_wait,
                         msat_make_or(menv, self.x_transm, self.x_retry)))
        # invars
        self.trans = msat_make_and(
            menv, self.trans,
            msat_make_impl(menv, self.x_transm,
                           msat_make_leq(menv, x_x, LAMBDA)))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_geq(menv, x_backoff, SIGMA))
        # (delta > 0 | evt_stutter) -> x' = x + delta & l' = l & backoff' = backoff
        lhs = msat_make_or(menv, msat_make_gt(menv, delta, nums[0]),
                           self.evt_stutter)
        rhs = msat_make_and(
            menv, same_loc,
            msat_make_and(menv,
                          msat_make_equal(menv, x_x,
                                          msat_make_plus(menv, x, delta)),
                          msat_make_equal(menv, x_backoff, backoff)))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))

        disc_t = msat_make_and(menv,
                               msat_make_not(menv, self.evt_stutter),
                               msat_make_equal(menv, delta, nums[0]))
        # l = wait -> (l' = wait | l' = transm | l' = retry) &
        # backoff' = backoff & x' = 0
        lhs = msat_make_and(menv, disc_t, self.wait)
        rhs = msat_make_or(menv,
                           msat_make_or(menv, self.x_wait, self.x_transm),
                           self.x_retry)
        rhs = msat_make_and(
            menv, rhs,
            msat_make_and(menv,
                          msat_make_equal(menv, x_backoff, backoff),
                          msat_make_equal(menv, x_x, nums[0])))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        # (l = wait & l' = wait) -> evt_cd
        lhs = msat_make_and(menv, msat_make_and(menv, disc_t, self.wait),
                            self.x_wait)
        rhs = self.evt_cd
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        # (l = wait & l' = transm) -> evt_begin
        lhs = msat_make_and(menv, msat_make_and(menv, disc_t, self.wait),
                            self.x_transm)
        rhs = self.evt_begin
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        # (l = wait & l' = retry) -> (evt_cd | evt_busy)
        lhs = msat_make_and(menv, msat_make_and(menv, disc_t, self.wait),
                            self.x_retry)
        rhs = msat_make_or(menv, self.evt_cd, self.evt_busy)
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        # (l = transm) -> (l' = wait | l' = retry) & x' = 0
        lhs = msat_make_and(menv, disc_t, self.transm)
        rhs = msat_make_and(menv,
                            msat_make_equal(menv, x_x, nums[0]),
                            msat_make_or(menv, self.x_wait, self.x_retry))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        # (l = transm & l' = wait) -> (evt_end & x >= LAMBDA & backoff' <= backoff)
        lhs = msat_make_and(menv, msat_make_and(menv, disc_t, self.transm),
                            self.x_wait)
        rhs = msat_make_and(
            menv,
            msat_make_geq(menv, x, LAMBDA),
            msat_make_and(menv, self.evt_end,
                          msat_make_leq(menv, x_backoff, backoff)))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        # (l = transm & l' = retry) -> (evt_cd & backoff' > backoff)
        lhs = msat_make_and(menv, msat_make_and(menv, disc_t, self.transm),
                            self.x_retry)
        rhs = msat_make_and(menv,
                            msat_make_geq(menv, x_backoff,
                                          msat_make_plus(menv, backoff,
                                                         nums[1])),
                            self.evt_cd)
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        # (l = retry) -> (l' = retry | l' = transm) & x' = 0 &
        # backoff' = backoff
        lhs = msat_make_and(menv, disc_t, self.retry)
        rhs = msat_make_and(
            menv,
            msat_make_or(menv, self.x_retry, self.x_transm),
            msat_make_and(menv,
                          msat_make_equal(menv, x_x, nums[0]),
                          msat_make_equal(menv, x_backoff, backoff)))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        # (l = retry & l' = retry) -> evt_cd
        lhs = msat_make_and(menv, msat_make_and(menv, disc_t, self.retry),
                            self.x_retry)
        rhs = self.evt_cd
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        # (l = retry & l' = transm) -> (evt_begin & x >= backoff)
        lhs = msat_make_and(menv, msat_make_and(menv, disc_t, self.retry),
                            self.x_transm)
        rhs = msat_make_and(menv,
                            self.evt_begin,
                            msat_make_geq(menv, x, backoff))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))


class Bus(Module):
    """Bus module"""
    def __init__(self, name: str, menv: msat_env, enc: LTLEncoder,
                 SIGMA, delta, x_delta):
        super().__init__(name, menv, enc)

        real_type = msat_get_rational_type(menv)
        bool_type = msat_get_bool_type(menv)

        evt_symbs, evts, x_evts = self._enum("evt", 5)
        loc_symbs, locs, x_locs = self._enum("l", 4)
        cd_id, x_cd_id = self._symb("cd_id", bool_type)
        x, x_x = self._symb("x", real_type)

        self.symb2next = {x: x_x, cd_id: x_cd_id}
        for s, x_s in chain(evt_symbs, loc_symbs):
            assert s not in self.symb2next
            self.symb2next[s] = x_s

        same_loc = msat_make_iff(menv, loc_symbs[0][1], loc_symbs[0][0])
        for s, x_s in loc_symbs[1:]:
            same_loc = msat_make_and(menv, same_loc,
                                     msat_make_iff(menv, x_s, s))
        same_cd_id = msat_make_iff(menv, x_cd_id, cd_id)

        nums = [msat_make_number(menv, str(idx)) for idx in range(5)]

        self.evt_stutter = evts[0]
        self.evt_begin = evts[1]
        self.evt_end = evts[2]
        self.evt_busy = evts[3]
        self.evt_cd = evts[4]

        x_evt_stutter = x_evts[0]
        x_evt_begin = x_evts[1]
        x_evt_end = x_evts[2]
        x_evt_busy = x_evts[3]
        x_evt_cd = x_evts[4]

        self.idle = locs[0]
        self.active = locs[1]
        self.collision = locs[2]
        self.transmit = locs[3]

        self.x_idle = x_locs[0]
        self.x_active = x_locs[1]
        self.x_collision = x_locs[2]
        self.x_transmit = x_locs[3]

        self.cd_id = cd_id

        # init: x = 0 & l = idle & cd_id
        self.init = msat_make_and(
            menv, self.idle,
            msat_make_and(menv, cd_id,
                          msat_make_equal(menv, x, nums[0])))

        # bound evt
        evt_bounds = msat_make_or(
            menv,
            self.evt_stutter,
            msat_make_or(menv,
                         msat_make_or(menv, self.evt_begin,
                                      self.evt_end),
                         msat_make_or(menv, self.evt_busy,
                                      self.evt_cd)))
        self.init = msat_make_and(menv, self.init, evt_bounds)
        evt_bounds = msat_make_or(
            menv,
            x_evt_stutter,
            msat_make_or(menv,
                         msat_make_or(menv, x_evt_begin, x_evt_end),
                         msat_make_or(menv, x_evt_busy, x_evt_cd)))
        self.trans = evt_bounds
        # bound loc
        loc_bounds = msat_make_or(menv,
                                  msat_make_or(menv, self.idle, self.active),
                                  msat_make_or(menv, self.collision,
                                               self.transmit))
        self.init = msat_make_and(menv, self.init, loc_bounds)
        loc_bounds = msat_make_or(menv,
                                  msat_make_or(menv, self.x_idle,
                                               self.x_active),
                                  msat_make_or(menv, self.x_collision,
                                               self.x_transmit))
        self.trans = msat_make_and(menv, self.trans, loc_bounds)

        # invars and urgent
        self.init = msat_make_and(
            menv, self.init,
            msat_make_and(menv,
                          msat_make_impl(menv, self.collision,
                                         msat_make_lt(menv, x, SIGMA)),
                          msat_make_impl(menv, self.transmit,
                                         msat_make_equal(menv, delta,
                                                         nums[0]))))
        self.trans = msat_make_and(
            menv, self.trans,
            msat_make_and(menv,
                          msat_make_impl(menv, self.x_collision,
                                         msat_make_lt(menv, x_x, SIGMA)),
                          msat_make_impl(menv, self.x_transmit,
                                         msat_make_equal(menv, x_delta,
                                                         nums[0]))))
        # (evt_stutter | delta > 0) -> x' = x + delta & l' = l & (cd_id' <-> cd_id)
        lhs = msat_make_or(menv, self.evt_stutter,
                           msat_make_gt(menv, delta, nums[0]))
        rhs = msat_make_and(
            menv,
            msat_make_and(menv,
                          msat_make_equal(menv, x_x,
                                          msat_make_plus(menv, x, delta)),
                          same_loc),
            same_cd_id)
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))

        d_eq_0 = msat_make_equal(menv, delta, nums[0])
        disc_t = msat_make_and(menv, msat_make_not(menv, self.evt_stutter),
                               d_eq_0)
        # (l = idle) -> (l' = active & evt_begin & cd_id' = cd_id & x' = 0)
        lhs = msat_make_and(menv, disc_t, self.idle)
        rhs = msat_make_and(menv,
                            msat_make_and(menv, self.x_active, self.evt_begin),
                            msat_make_and(menv, same_cd_id,
                                          msat_make_equal(menv, x_x, nums[0])))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        # (l = active) -> (l' = idle | l' = active | l' = collision)
        lhs = msat_make_and(menv, disc_t, self.active)
        rhs = msat_make_or(menv, self.x_idle, self.x_active)
        rhs = msat_make_or(menv, rhs, self.x_collision)
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        # (l = active & l' = idle) -> (evt_end & x' = 0 & cd_id' = cd_id)
        lhs = msat_make_and(menv, disc_t,
                            msat_make_and(menv, self.active, self.x_idle))
        rhs = msat_make_and(menv, self.evt_end,
                            msat_make_and(menv,
                                          msat_make_equal(menv, x_x, nums[0]),
                                          same_cd_id))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        # (l = active & l' = active) -> (evt_busy & x >= SIGMA & x' = x &
        # cd_id' = cd_id)
        lhs = msat_make_and(menv, disc_t,
                            msat_make_and(menv, self.active, self.x_active))
        rhs = msat_make_and(menv,
                            msat_make_and(menv, self.evt_busy,
                                          msat_make_geq(menv, x, SIGMA)),
                            msat_make_and(menv,
                                          msat_make_equal(menv, x_x, x),
                                          same_cd_id))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        # (l = active & l' = collision) -> (evt_begin & x < SIGMA & x' = 0)
        lhs = msat_make_and(menv, disc_t,
                            msat_make_and(menv, self.active, self.x_collision))
        rhs = msat_make_and(menv, self.evt_begin,
                            msat_make_and(menv,
                                          msat_make_lt(menv, x, SIGMA),
                                          msat_make_equal(menv, x_x, nums[0])))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        # (l = collision) -> (l' = transmit & x < SIGMA & evt_cd &
        # x' = 0 & cd_id' != cd_id)
        lhs = msat_make_and(menv, disc_t, self.collision)
        rhs = msat_make_and(
            menv,
            msat_make_and(menv, self.x_transmit,
                          msat_make_lt(menv, x, SIGMA)),
            msat_make_and(menv, self.evt_cd,
                          msat_make_equal(menv, x_x, nums[0])))
        rhs = msat_make_and(menv, rhs,
                            msat_make_not(menv, same_cd_id))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        # (l = transmit) ->  l' = idle & x' = 0 & same_cd_id
        lhs = msat_make_and(menv, disc_t, self.transmit)
        rhs = msat_make_and(menv, self.x_idle,
                            msat_make_and(menv,
                                          msat_make_equal(menv, x_x, nums[0]),
                                          same_cd_id))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
