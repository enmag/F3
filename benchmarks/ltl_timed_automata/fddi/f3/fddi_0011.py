from collections import Iterable
from itertools import chain
from math import log, ceil

from mathsat import msat_term, msat_env
from mathsat import msat_make_constant, msat_declare_function
from mathsat import msat_get_rational_type, msat_get_integer_type, \
    msat_get_bool_type
from mathsat import msat_make_and, msat_make_not, msat_make_or, msat_make_iff
from mathsat import msat_make_leq, msat_make_equal, msat_make_true
from mathsat import msat_make_number, msat_make_plus, msat_make_times

from ltl.ltl import TermMap, LTLEncoder
from utils import name_next

num_procs = 11
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

    N = msat_make_number(menv, str(num_procs - 1))
    SA = msat_make_number(menv, "20")
    TD = msat_make_number(menv, "0")
    TRTT = msat_make_number(menv, "120")

    delta, x_delta = decl_consts(menv, delta_name, real_type)

    curr2next = {delta: x_delta}

    r = Ring("r", menv, enc, N, TD, delta)
    sts = [ST("s{}".format(idx), menv, enc, idx, SA, TRTT, delta)
           for idx in range(num_procs)]

    components = [r, *sts]
    for comp in components:
        for s, x_s in comp.symb2next.items():
            assert s not in curr2next.keys()
            curr2next[s] = x_s

    zero = msat_make_number(menv, "0")

    # invar delta >= 0
    init = msat_make_geq(menv, delta, zero)
    trans = msat_make_geq(menv, x_delta, zero)
    for comp in components:
        init = msat_make_and(menv, init, comp.init)
        trans = msat_make_and(menv, trans, comp.trans)

    d_eq_0 = msat_make_equal(menv, delta, zero)

    # not all stutter
    not_all_stutter = msat_make_not(menv, r.evt_stutter)
    for s in sts:
        not_all_stutter = msat_make_or(menv, not_all_stutter,
                                       msat_make_not(menv, s.evt_stutter))
    trans = msat_make_and(menv, trans,
                          msat_make_impl(menv, d_eq_0, not_all_stutter))

    # sync ring and sts
    for idx, s in enumerate(sts):
        idx = msat_make_number(menv, str(idx))
        rt = msat_make_iff(menv, s.evt_rt,
                           msat_make_and(menv, r.evt_rt,
                                         msat_make_equal(menv, r.evt_id, idx)))
        trans = msat_make_and(menv, trans,
                              msat_make_impl(menv, d_eq_0, rt))
        tt = msat_make_iff(menv, s.evt_tt,
                           msat_make_and(menv, r.evt_tt,
                                         msat_make_equal(menv, r.evt_id, idx)))
        trans = msat_make_and(menv, trans,
                              msat_make_impl(menv, d_eq_0, tt))

    # (G F st0.y_async) -> (G F r.l = ring_to_counter)
    ltl = enc.make_G(enc.make_F(sts[0].y_async))
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


class Ring(Module):
    """Ring module"""
    def __init__(self, name: str, menv: msat_env, enc: LTLEncoder,
                 N, TD, delta):
        super().__init__(name, menv, enc)

        int_type = msat_get_integer_type(menv)
        real_type = msat_get_rational_type(menv)
        bool_type = msat_get_bool_type(menv)

        # evt, x_evt = self._symb("event", int_type)
        evt_symbs, evts, x_evts = self._enum("event", 3)
        loc, x_loc = self._symb("l", bool_type)
        evt_id, x_evt_id = self._symb("evt_id", int_type)
        counter, x_counter = self._symb("counter", int_type)
        x, x_x = self._symb("x", real_type)

        self.symb2next = {evt_id: x_evt_id, counter: x_counter,
                          loc: x_loc, x: x_x}
        for s, x_s in evt_symbs:
            assert s not in self.symb2next
            self.symb2next[s] = x_s

        nums = [msat_make_number(menv, str(n))
                for n in range(3)]

        self.evt_stutter = evts[0]
        self.evt_rt = evts[1]
        self.evt_tt = evts[2]
        x_evt_stutter = x_evts[0]
        x_evt_rt = x_evts[1]
        x_evt_tt = x_evts[2]

        self.ring_to_counter = loc
        self.ring_counter = msat_make_not(menv, loc)
        self.x_ring_to_counter = x_loc
        self.x_ring_counter = msat_make_not(menv, x_loc)

        self.evt_id = evt_id

        # l = ring_to_counter & counter = 0 & x = 0
        self.init = msat_make_and(menv, self.ring_to_counter,
                                  msat_make_and(
                                      menv,
                                      msat_make_equal(menv, counter, nums[0]),
                                      msat_make_equal(menv, x, nums[0])))
        # bound evt
        bound_evt = msat_make_or(menv, self.evt_stutter,
                                 msat_make_or(menv, self.evt_rt,
                                              self.evt_tt))
        self.init = msat_make_and(menv, self.init, bound_evt)
        bound_evt = msat_make_or(menv, x_evt_stutter,
                                 msat_make_or(menv, x_evt_rt,
                                              x_evt_tt))
        self.trans = msat_make_and(menv, self.trans, bound_evt)

        # bound evt_id
        bound_evt_id = msat_make_equal(menv, evt_id, nums[0])
        x_bound_evt_id = msat_make_equal(menv, x_evt_id, nums[0])
        for idx in range(1, num_procs):
            num = msat_make_number(menv, str(idx))
            bound_evt_id = msat_make_or(menv, bound_evt_id,
                                        msat_make_equal(menv, evt_id, num))
            x_bound_evt_id = msat_make_or(menv, x_bound_evt_id,
                                          msat_make_equal(menv, x_evt_id, num))
        self.init = msat_make_and(menv, self.init, bound_evt_id)
        self.trans = x_bound_evt_id

        # bound counter
        bound_counter = msat_make_equal(menv, counter, nums[0])
        x_bound_counter = msat_make_equal(menv, x_counter, nums[0])
        for idx in range(1, num_procs):
            num = msat_make_number(menv, str(idx))
            bound_counter = msat_make_or(menv, bound_counter,
                                         msat_make_equal(menv, counter, num))
            x_bound_counter = msat_make_or(menv, x_bound_counter,
                                           msat_make_equal(menv, x_counter,
                                                           num))
        self.init = msat_make_and(menv, self.init, bound_counter)
        self.trans = msat_make_and(menv, self.trans, x_bound_counter)

        # invars
        self.init = msat_make_and(
            menv, self.init,
            msat_make_impl(menv, self.ring_to_counter,
                           msat_make_leq(menv, x, TD)))
        self.trans = msat_make_and(
            menv, self.trans,
            msat_make_impl(menv, self.x_ring_to_counter,
                           msat_make_leq(menv, x_x, TD)))

        # delta > 0 -> x' = x + delta & l' <-> l & counter' = counter
        self.trans = msat_make_and(
            menv, self.trans,
            msat_make_impl(
                menv, msat_make_gt(menv, delta, nums[0]),
                msat_make_and(
                    menv,
                    msat_make_equal(menv, x_x,
                                    msat_make_plus(menv, x, delta)),
                    msat_make_and(menv,
                                  msat_make_iff(menv, x_loc, loc),
                                  msat_make_equal(menv, x_counter, counter)))))

        # evt_stutter -> l' <-> l & x' = x + delta & counter' = counter
        self.trans = msat_make_and(
            menv, self.trans,
            msat_make_impl(menv, self.evt_stutter,
                           msat_make_and(
                               menv,
                               msat_make_iff(menv, x_loc, loc),
                               msat_make_and(
                                   menv,
                                   msat_make_equal(menv, x_x,
                                                   msat_make_plus(menv, x,
                                                                  delta)),
                                   msat_make_equal(menv, x_counter,
                                                   counter)))))

        d_eq_0 = msat_make_equal(menv, delta, nums[0])
        disc_t = msat_make_and(menv,
                               msat_make_not(menv, self.evt_stutter),
                               d_eq_0)
        # (l = ring_to_counter) -> (x <= TD & evt_tt & evt_id = counter &
        # l' = ring_counter & x' = x & counter' = counter)
        lhs = msat_make_and(menv, disc_t, self.ring_to_counter)
        rhs = msat_make_and(menv,
                            msat_make_and(menv,
                                          msat_make_leq(menv, x, TD),
                                          self.evt_tt),
                            msat_make_and(menv,
                                          msat_make_equal(menv, evt_id,
                                                          counter),
                                          self.x_ring_counter))
        rhs = msat_make_and(menv, rhs,
                            msat_make_and(menv,
                                          msat_make_equal(menv, x_x, x),
                                          msat_make_equal(menv, x_counter,
                                                          counter)))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        # (l = ring_counter & counter < N) -> (evt_rt & evt_id = counter &
        # x' = 0 & counter' = counter + 1 & l' = ring_to_counter)
        lhs = msat_make_and(menv, disc_t,
                            msat_make_and(menv,
                                          self.ring_counter,
                                          msat_make_lt(menv, counter, N)))
        rhs = msat_make_and(
            menv,
            msat_make_and(menv, self.evt_rt,
                          msat_make_equal(menv, evt_id, counter)),
            msat_make_and(menv, msat_make_equal(menv, x_x, nums[0]),
                          msat_make_equal(menv, x_counter,
                                          msat_make_plus(menv, counter,
                                                         nums[1]))))
        rhs = msat_make_and(menv, rhs, self.x_ring_to_counter)
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        # (l = ring_counter & counter = N) -> (evt_rt & evt_id = counter &
        # x' = 0 & counter' = 0 & l' = ring_to_counter)
        lhs = msat_make_and(menv, disc_t,
                            msat_make_and(menv,
                                          self.ring_counter,
                                          msat_make_equal(menv, counter, N)))
        rhs = msat_make_and(
            menv,
            msat_make_and(menv, self.evt_rt,
                          msat_make_equal(menv, evt_id, counter)),
            msat_make_and(menv,
                          msat_make_equal(menv, x_x, nums[0]),
                          msat_make_equal(menv, x_counter, nums[0])))
        rhs = msat_make_and(menv, rhs, self.x_ring_to_counter)
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))


class ST(Module):
    """ST module"""
    def __init__(self, name: str, menv: msat_env, enc: LTLEncoder,
                 idx, SA, TRTT, delta):
        super().__init__(name, menv, enc)

        # int_type = msat_get_integer_type(menv)
        real_type = msat_get_rational_type(menv)

        # evt, x_evt = self._symb("evt", int_type)
        evt_symbs, evts, x_evts = self._enum("evt", 4)
        # loc, x_loc = self._symb("l", int_type)
        loc_symbs, locs, x_locs = self._enum("l", 6)
        x, x_x = self._symb("x", real_type)
        y, x_y = self._symb("y", real_type)
        z, x_z = self._symb("z", real_type)

        self.symb2next = {x: x_x, y: x_y, z: x_z}
        for s, x_s in chain(evt_symbs, loc_symbs):
            assert s not in self.symb2next
            self.symb2next[s] = x_s

        nums = [msat_make_number(menv, str(idx)) for idx in range(6)]

        self.evt_stutter = evts[0]
        self.evt_move = evts[1]
        self.evt_rt = evts[2]
        self.evt_tt = evts[3]
        x_evt_stutter = x_evts[0]
        x_evt_move = x_evts[1]
        x_evt_rt = x_evts[2]
        x_evt_tt = x_evts[3]

        self.z_idle = locs[0]
        self.z_sync = locs[1]
        self.z_async = locs[2]
        self.y_idle = locs[3]
        self.y_sync = locs[4]
        self.y_async = locs[5]
        self.x_z_idle = x_locs[0]
        self.x_z_sync = x_locs[1]
        self.x_z_async = x_locs[2]
        self.x_y_idle = x_locs[3]
        self.x_y_sync = x_locs[4]
        self.x_y_async = x_locs[5]

        same_loc = msat_make_iff(menv, loc_symbs[0][1], loc_symbs[0][0])
        for s, x_s in loc_symbs[1:]:
            same_loc = msat_make_and(menv, same_loc,
                                     msat_make_iff(menv, x_s, s))

        evt_bound = msat_make_or(
            menv,
            msat_make_or(menv, self.evt_stutter, self.evt_move),
            msat_make_or(menv, self.evt_rt, self.evt_tt))
        loc_bound = msat_make_or(menv,
                                 msat_make_or(menv, self.z_idle, self.z_sync),
                                 msat_make_or(menv, self.z_async, self.y_idle))
        loc_bound = msat_make_or(menv, loc_bound,
                                 msat_make_or(menv, self.y_sync, self.y_async))
        self.init = msat_make_and(menv, evt_bound, loc_bound)

        evt_bound = msat_make_or(
            menv,
            msat_make_or(menv, x_evt_stutter, x_evt_move),
            msat_make_or(menv, x_evt_rt, x_evt_tt))
        loc_bound = msat_make_or(menv,
                                 msat_make_or(menv, self.x_z_idle,
                                              self.x_z_sync),
                                 msat_make_or(menv, self.x_z_async,
                                              self.x_y_idle))
        loc_bound = msat_make_or(menv, loc_bound,
                                 msat_make_or(menv, self.x_y_sync,
                                              self.x_y_async))
        self.trans = msat_make_and(menv, evt_bound, loc_bound)

        # l = z_idle & x = 0 & y = 0 & z = 0
        curr = msat_make_and(menv,
                             msat_make_and(menv, self.z_idle,
                                           msat_make_equal(menv, x, nums[0])),
                             msat_make_and(menv,
                                           msat_make_equal(menv, y, nums[0]),
                                           msat_make_equal(menv, z, nums[0])))
        self.init = msat_make_and(menv, self.init, curr)

        # invars
        # l = z_sync -> x <= SA
        self.init = msat_make_and(menv, self.init,
                                  msat_make_impl(menv, self.z_sync,
                                                 msat_make_leq(menv, x, SA)))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, self.x_z_sync,
                                                  msat_make_leq(menv, x_x,
                                                                SA)))
        # l = z_async -> x <= TRTT
        self.init = msat_make_and(menv, self.init,
                                  msat_make_impl(menv, self.z_async,
                                                 msat_make_leq(menv, x, TRTT)))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, self.x_z_async,
                                                  msat_make_leq(menv, x_x,
                                                                TRTT)))
        # l = y_sync -> x <= SA
        # self.init = msat_make_and(menv, self.init,
        #                           msat_make_impl(menv, self.y_sync,
        #                                          msat_make_leq(menv, x, SA)))
        # self.trans = msat_make_and(
        #     menv, self.trans,
        #     msat_make_impl(menv, self.x_y_sync,
        #                    msat_make_leq(menv, x_x, SA)))

        # l = y_async -> x <= TRTT
        self.init = msat_make_and(menv, self.init,
                                  msat_make_impl(menv, self.y_async,
                                                 msat_make_leq(menv, x, TRTT)))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, self.x_y_async,
                                                  msat_make_leq(menv, x_x,
                                                                TRTT)))

        x_p_delta = msat_make_equal(menv, x_x,
                                    msat_make_plus(menv, x, delta))
        y_p_delta = msat_make_equal(menv, x_y,
                                    msat_make_plus(menv, y, delta))
        z_p_delta = msat_make_equal(menv, x_z,
                                    msat_make_plus(menv, z, delta))
        # delta > 0 -> x' = x + delta & y' = y + delta & z' = z + delta & l' = l
        lhs = msat_make_gt(menv, delta, nums[0])
        rhs = msat_make_and(
            menv,
            msat_make_and(menv, x_p_delta, y_p_delta),
            msat_make_and(menv, z_p_delta, same_loc))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        # evt_stutter -> l' = l & x' = x + delta & y' = y + delta & z' = z + delta
        lhs = self.evt_stutter
        rhs = msat_make_and(menv,
                            msat_make_and(menv, same_loc,
                                          x_p_delta),
                            msat_make_and(menv, y_p_delta, z_p_delta))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))

        disc_t = msat_make_and(menv, msat_make_equal(menv, delta, nums[0]),
                               msat_make_not(menv, self.evt_stutter))
        # (l = z_idle) -> (evt_tt & l' = z_sync & x' = 0 & y' = 0 & z' = z)
        lhs = msat_make_and(menv, disc_t, self.z_idle)
        rhs = msat_make_and(menv,
                            msat_make_and(menv, self.evt_tt, self.x_z_sync),
                            msat_make_and(menv,
                                          msat_make_equal(menv, x_x, nums[0]),
                                          msat_make_equal(menv, x_y, nums[0])))
        rhs = msat_make_and(menv, rhs, msat_make_equal(menv, x_z, z))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        # (l = z_sync) -> ((l' = z_async | l' = y_idle) & x' = x & y' = y & z' = z)
        lhs = msat_make_and(menv, disc_t, self.z_sync)
        rhs = msat_make_and(
            menv,
            msat_make_and(menv,
                          msat_make_or(menv, self.x_z_async, self.x_y_idle),
                          msat_make_equal(menv, x_x, x)),
            msat_make_and(menv, msat_make_equal(menv, x_y, y),
                          msat_make_equal(menv, x_z, z)))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        # (l = z_sync & next(l) = z_async) -> (x >= SA & z < TRTT & evt_move)
        lhs = msat_make_and(menv, disc_t,
                            msat_make_and(menv, self.z_sync, self.x_z_async))
        rhs = msat_make_and(menv,
                            msat_make_and(menv, msat_make_geq(menv, x, SA),
                                          msat_make_lt(menv, z, TRTT)),
                            self.evt_move)
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        # (l = z_sync & next(l) = y_idle) -> (x >= SA & z >= TRTT & evt_rt)
        lhs = msat_make_and(menv, disc_t,
                            msat_make_and(menv, self.z_sync, self.x_y_idle))
        rhs = msat_make_and(menv, self.evt_rt,
                            msat_make_and(menv, msat_make_geq(menv, x, SA),
                                          msat_make_geq(menv, z, TRTT)))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        # (l = z_async) -> (l' = y_idle & evt_rt & x' = x & y' = y & z' = z)
        lhs = msat_make_and(menv, disc_t, self.z_async)
        rhs = msat_make_and(menv,
                            msat_make_and(menv, self.x_y_idle, self.evt_rt),
                            msat_make_and(menv,
                                          msat_make_equal(menv, x_x, x),
                                          msat_make_equal(menv, x_y, y)))
        rhs = msat_make_and(menv, rhs, msat_make_equal(menv, x_z, z))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        # (l = y_idle) -> (l' = y_sync & evt_tt & x' = 0 & y' = y & z' = 0)
        lhs = msat_make_and(menv, disc_t, self.y_idle)
        rhs = msat_make_and(menv,
                            msat_make_and(menv, self.x_y_sync, self.evt_tt),
                            msat_make_and(menv,
                                          msat_make_equal(menv, x_x, nums[0]),
                                          msat_make_equal(menv, x_y, y)))
        rhs = msat_make_and(menv, rhs, msat_make_equal(menv, x_z, nums[0]))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        # (l = y_sync) -> ((l' = y_async | l' = z_idle) & x' = x & y' = y & z' = z)
        lhs = msat_make_and(menv, disc_t, self.y_sync)
        rhs = msat_make_and(
            menv,
            msat_make_and(menv, msat_make_equal(menv, x_x, x),
                          msat_make_equal(menv, x_y, y)),
            msat_make_and(menv, msat_make_equal(menv, x_z, z),
                          msat_make_or(menv, self.x_y_async, self.x_z_idle)))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        # (l = y_sync & next(l) = y_async) -> (x >= SA & y < TRTT & evt_move)
        lhs = msat_make_and(menv, disc_t,
                            msat_make_and(menv, self.y_sync, self.x_y_async))
        rhs = msat_make_and(menv,
                            msat_make_geq(menv, x, SA),
                            msat_make_lt(menv, y, TRTT))
        rhs = msat_make_and(menv, rhs, self.evt_move)
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        # (l = y_sync & next(l) = z_idle) -> (x >= SA & y >= TRTT & evt_rt)
        lhs = msat_make_and(menv, disc_t,
                            msat_make_and(menv, self.y_sync, self.x_z_idle))
        rhs = msat_make_and(menv,
                            msat_make_geq(menv, x, SA),
                            msat_make_geq(menv, y, TRTT))
        rhs = msat_make_and(menv, rhs, self.evt_rt)
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        # (l = y_async) -> (l' = z_idle & evt_rt & x' = x & y' = y & z' = z)
        lhs = msat_make_and(menv, disc_t, self.y_async)
        rhs = msat_make_and(menv,
                            msat_make_and(menv, self.x_z_idle, self.evt_rt),
                            msat_make_and(menv,
                                          msat_make_equal(menv, x_x, x),
                                          msat_make_equal(menv, x_y, y)))
        rhs = msat_make_and(menv, rhs, msat_make_equal(menv, x_z, z))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
