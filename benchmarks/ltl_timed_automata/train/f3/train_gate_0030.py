from typing import Iterable, Tuple
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
from expr_utils import name2next

num_procs = 30
delta_name = "delta"


def decl_consts(menv: msat_env, name: str, c_type):
    assert not name.startswith("_"), name
    s = msat_declare_function(menv, name, c_type)
    s = msat_make_constant(menv, s)
    x_s = msat_declare_function(menv, name2next(name), c_type)
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


def check_ltl(menv: msat_env, enc: LTLEncoder) -> Tuple[Iterable, msat_term,
                                                   msat_term, msat_term]:
    assert menv
    assert isinstance(menv, msat_env)
    assert enc
    assert isinstance(enc, LTLEncoder)
    real_type = msat_get_rational_type(menv)

    delta, x_delta = decl_consts(menv, delta_name, real_type)

    curr2next = {delta: x_delta}

    a = msat_make_number(menv, "2")
    b = msat_make_number(menv, "5")
    c = msat_make_number(menv, "1")
    d = msat_make_number(menv, "2")
    e = msat_make_number(menv, "1")

    gate = Gate("gate", menv, enc, c, d, delta)
    controller = Controller("controller", menv, enc, e, num_procs + 1,
                            delta)
    trains = [Train("t{}".format(idx), menv, enc, a, b, delta)
              for idx in range(num_procs)]
    components = [gate, controller, *trains]
    for p in components:
        for s, x_s in p.symb2next.items():
            assert s not in curr2next.keys()
            curr2next[s] = x_s

    zero = msat_make_number(menv, "0")

    # delta > 0
    init = msat_make_geq(menv, delta, zero)
    trans = msat_make_geq(menv, x_delta, zero)

    for p in components:
        init = msat_make_and(menv, init, p.init)
        trans = msat_make_and(menv, trans, p.trans)

    d_eq_0 = msat_make_equal(menv, delta, zero)

    # only 1 train moves
    for idx0, t0 in enumerate(trains):
        other_stutter = None
        for idx1, t1 in enumerate(trains):
            if idx0 != idx1:
                if other_stutter is None:
                    other_sutter = t1.evt_stutter
                else:
                    other_sutter = msat_make_and(menv, other_sutter,
                                                 t1.evt_stutter)
        lhs = msat_make_and(menv, d_eq_0,
                            msat_make_not(menv, t0.evt_stutter))
        curr = msat_make_impl(menv, lhs, other_sutter)
        trans = msat_make_and(menv, trans, curr)

    # sync evt_lower
    trans = msat_make_and(menv, trans,
                          msat_make_impl(
                              menv, d_eq_0,
                              msat_make_iff(menv, controller.evt_lower,
                                            gate.evt_lower)))
    # sync evt_rise
    trans = msat_make_and(menv, trans,
                          msat_make_impl(
                              menv, d_eq_0,
                              msat_make_iff(menv, controller.evt_rise,
                                            gate.evt_rise)))
    # sync evt_approach
    train_approach = trains[0].evt_approach
    for t in trains[1:]:
        train_approach = msat_make_or(menv, train_approach, t.evt_approach)
    trans = msat_make_and(menv, trans,
                          msat_make_impl(
                              menv, d_eq_0,
                              msat_make_iff(menv, controller.evt_approach,
                                            train_approach)))
    # sync evt_exit
    train_exit = trains[0].evt_exit
    for t in trains[1:]:
        train_exit = msat_make_or(menv, train_exit, t.evt_exit)
    trans = msat_make_and(menv, trans,
                          msat_make_impl(
                              menv, d_eq_0,
                              msat_make_iff(menv, controller.evt_exit,
                                            train_exit)))

    # G ((gate.g0 & gate.g1') -> F (gate.g2 & gate.g3'))
    lhs = msat_make_and(menv, gate.g0, enc.make_X(gate.g1))
    rhs = msat_make_and(menv, gate.g2, enc.make_X(gate.g3))
    ltl = enc.make_G(msat_make_impl(menv, lhs, enc.make_F(rhs)))
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


class Train(Module):
    """Train module"""
    def __init__(self, name: str, menv: msat_env, enc: LTLEncoder,
                 a, b, delta):
        super().__init__(name, menv, enc)

        # int_type = msat_get_integer_type(menv)
        real_type = msat_get_rational_type(menv)

        # loc, x_loc = self._symb("l", int_type)
        loc_symbs, locs, x_locs = self._enum("l", 4)
        # evt, x_evt = self._symb("evt", int_type)
        evt_symbs, evts, x_evts = self._enum("evt", 4)
        x, x_x = self._symb("x", real_type)

        self.symb2next = {x: x_x}
        for s, x_s in chain(evt_symbs, loc_symbs):
            assert s not in self.symb2next
            self.symb2next[s] = x_s

        self.evt_stutter = evts[0]
        self.evt_approach = evts[1]
        self.evt_exit = evts[2]
        self.evt_move = evts[3]
        x_evt_stutter = x_evts[0]
        x_evt_approach = x_evts[1]
        x_evt_exit = x_evts[2]
        x_evt_move = x_evts[3]

        self.t0 = locs[0]
        self.t1 = locs[1]
        self.t2 = locs[2]
        self.t3 = locs[3]
        self.x_t0 = x_locs[0]
        self.x_t1 = x_locs[1]
        self.x_t2 = x_locs[2]
        self.x_t3 = x_locs[3]

        same_loc = msat_make_iff(menv, loc_symbs[0][1], loc_symbs[0][0])
        for s, x_s in loc_symbs[1:]:
            same_loc = msat_make_and(menv, same_loc,
                                     msat_make_iff(menv, x_s, s))

        zero = msat_make_number(menv, "0")

        # l = t0 & x = 0
        self.init = msat_make_and(menv, self.t0,
                                  msat_make_equal(menv, x, zero))
        # bound l
        bound_l = msat_make_or(menv,
                               msat_make_or(menv, self.t0, self.t1),
                               msat_make_or(menv, self.t2, self.t3))
        self.init = msat_make_and(menv, self.init, bound_l)
        x_bound_l = msat_make_or(menv,
                                 msat_make_or(menv, self.x_t0, self.x_t1),
                                 msat_make_or(menv, self.x_t2, self.x_t3))
        self.trans = x_bound_l

        # bound evt
        bound_evt = msat_make_or(menv,
                                 msat_make_or(menv, self.evt_stutter,
                                              self.evt_approach),
                                 msat_make_or(menv, self.evt_exit,
                                              self.evt_move))
        self.init = msat_make_and(menv, self.init, bound_evt)
        x_bound_evt = msat_make_or(menv,
                                   msat_make_or(menv, x_evt_stutter,
                                                x_evt_approach),
                                   msat_make_or(menv, x_evt_exit,
                                                x_evt_move))
        self.trans = msat_make_and(menv, self.trans, x_bound_evt)

        # invars: l != t0 -> x <= b
        lhs = msat_make_not(menv, self.t0)
        rhs = msat_make_leq(menv, x, b)
        self.init = msat_make_and(menv, self.init,
                                  msat_make_impl(menv, lhs, rhs))
        # invars: l != t0 -> x <= b
        lhs = msat_make_not(menv, self.x_t0)
        rhs = msat_make_leq(menv, x_x, b)
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))

        # delta > 0 | stutter -> x' = x + delta & l' = l
        lhs = msat_make_or(menv, msat_make_gt(menv, delta, zero),
                           self.evt_stutter)
        rhs = msat_make_and(menv,
                            msat_make_equal(menv, x_x,
                                            msat_make_plus(menv, x, delta)),
                            same_loc)
        self.trans = msat_make_and( menv, self.trans,
                                    msat_make_impl(menv, lhs, rhs))

        disc_t = msat_make_and(menv, msat_make_equal(menv, delta, zero),
                               msat_make_not(menv, self.evt_stutter))

        # (l = t0) -> (l' = t1 & evt_approach & x' = 0)
        lhs = msat_make_and(menv, disc_t, self.t0)
        rhs = msat_make_and(menv,
                            msat_make_and(menv, self.x_t1,
                                          self.evt_approach),
                            msat_make_equal(menv, x_x, zero))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        # (l = t1) -> (l' = t2 & x > a & evt_move & x' = x)
        lhs = msat_make_and(menv, disc_t, self.t1)
        rhs = msat_make_and(menv,
                            msat_make_and(menv, self.x_t2,
                                          msat_make_gt(menv, x, a)),
                            msat_make_and(menv, self.evt_move,
                                          msat_make_equal(menv, x_x, x)))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        # (l = t2) -> (l' = t3 & evt_move & x' = x)
        lhs = msat_make_and(menv, disc_t, self.t2)
        rhs = msat_make_and(menv,
                            msat_make_and(menv, self.x_t3, self.evt_move),
                            msat_make_equal(menv, x_x, x))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        # (l = t3) -> (l' = t0 & x <= b & evt_exit & x' = x)
        lhs = msat_make_and(menv, disc_t, self.t3)
        rhs = msat_make_and(menv,
                            msat_make_and(menv, self.x_t0,
                                          msat_make_leq(menv, x, b)),
                            msat_make_and(menv, self.evt_exit,
                                          msat_make_equal(menv, x_x, x)))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))


class Gate(Module):
    """Gate module"""
    def __init__(self, name: str, menv: msat_env, enc: LTLEncoder,
                 c, d, delta):
        super().__init__(name, menv, enc)

        real_type = msat_get_rational_type(menv)

        loc_symbs, locs, x_locs = self._enum("l", 4)
        evt_symbs, evts, x_evts = self._enum("evt", 4)
        y, x_y = self._symb("y", real_type)

        self.symb2next = {y: x_y}
        for s, x_s in chain(loc_symbs, evt_symbs):
            assert s not in self.symb2next
            self.symb2next[s] = x_s

        self.evt_stutter = evts[0]
        self.evt_lower = evts[1]
        self.evt_rise = evts[2]
        self.evt_move = evts[3]
        x_evt_stutter = x_evts[0]
        x_evt_lower = x_evts[1]
        x_evt_rise = x_evts[2]
        x_evt_move = x_evts[3]

        self.g0 = locs[0]
        self.g1 = locs[1]
        self.g2 = locs[2]
        self.g3 = locs[3]
        self.x_g0 = x_locs[0]
        self.x_g1 = x_locs[1]
        self.x_g2 = x_locs[2]
        self.x_g3 = x_locs[3]

        same_loc = msat_make_iff(menv, loc_symbs[0][1], loc_symbs[0][0])
        for s, x_s in loc_symbs[1:]:
            same_loc = msat_make_and(menv, same_loc,
                                     msat_make_iff(menv, x_s, s))

        zero = msat_make_number(menv, "0")
        # l = g0 & y = 0
        self.init = msat_make_and(menv, self.g0,
                                  msat_make_equal(menv, y, zero))
        # bound l
        bound_l = msat_make_or(menv,
                               msat_make_or(menv, self.g0, self.g1),
                               msat_make_or(menv, self.g2, self.g3))
        self.init = msat_make_and(menv, self.init, bound_l)
        x_bound_l = msat_make_or(menv,
                                 msat_make_or(menv, self.x_g0, self.x_g1),
                                 msat_make_or(menv, self.x_g2, self.x_g3))
        self.trans = x_bound_l
        # bound evt
        bound_evt = msat_make_or(menv,
                                 msat_make_or(menv, self.evt_stutter,
                                              self.evt_lower),
                                 msat_make_or(menv, self.evt_rise,
                                              self.evt_move))
        self.init = msat_make_and(menv, self.init, bound_evt)
        x_bound_evt = msat_make_or(menv,
                                   msat_make_or(menv, x_evt_stutter,
                                                x_evt_lower),
                                   msat_make_or(menv, x_evt_rise,
                                                x_evt_move))
        self.trans = msat_make_and(menv, self.trans, x_bound_evt)

        # invars: l = g1 -> y <= c; l = g3 -> y <= d
        lhs = self.g1
        rhs = msat_make_leq(menv, y, c)
        self.init = msat_make_and(menv, self.init,
                                  msat_make_impl(menv, lhs, rhs))
        lhs = self.g3
        rhs = msat_make_leq(menv, y, d)
        self.init = msat_make_and(menv, self.init,
                                  msat_make_impl(menv, lhs, rhs))
        # invars: l = g1 -> y <= c; l = g3 -> y <= d
        lhs = self.x_g1
        rhs = msat_make_leq(menv, x_y, c)
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        lhs = self.x_g3
        rhs = msat_make_leq(menv, x_y, d)
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))

        # delta > 0 | stutter -> y' = y + delta & l' = l
        lhs = msat_make_or(menv,
                           msat_make_gt(menv, delta, zero),
                           self.evt_stutter)
        rhs = msat_make_and(menv,
                            msat_make_equal(menv, x_y,
                                            msat_make_plus(menv, y, delta)),
                            same_loc)
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))

        disc_t = msat_make_and(menv, msat_make_equal(menv, delta, zero),
                               msat_make_not(menv, self.evt_stutter))

        # (l = g0) -> (l' = g1 & evt_lower & y' = 0)
        lhs = msat_make_and(menv, disc_t, self.g0)
        rhs = msat_make_and(menv,
                            msat_make_and(menv, self.x_g1,
                                          self.evt_lower),
                            msat_make_equal(menv, x_y, zero))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        # (l = g1) -> (l' = g2 & y <= c & evt_move & y' = y)
        lhs = msat_make_and(menv, disc_t, self.g1)
        rhs = msat_make_and(menv,
                            msat_make_and(menv, self.x_g2,
                                          self.evt_move),
                            msat_make_and(menv,
                                          msat_make_leq(menv, y, c),
                                          msat_make_equal(menv, x_y, y)))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        # (l = g2) -> (l' = g3 & evt_rise & y' = 0)
        lhs = msat_make_and(menv, disc_t, self.g2)
        rhs = msat_make_and(menv,
                            msat_make_and(menv, self.x_g3, self.evt_rise),
                            msat_make_equal(menv, x_y, zero))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        # (l = g3) -> (l' = g0 & y >= c & y <= d & evt_move & y' = y)
        lhs = msat_make_and(menv, disc_t, self.g3)
        rhs = msat_make_and(menv,
                            msat_make_and(menv, self.x_g0,
                                          msat_make_geq(menv, y, c)),
                            msat_make_and(menv,
                                          msat_make_leq(menv, y, d),
                                          self.evt_move))
        rhs = msat_make_and(menv, rhs,
                            msat_make_equal(menv, x_y, y))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))


class Controller(Module):
    """Controller module"""
    def __init__(self, name: str, menv: msat_env, enc: LTLEncoder,
                 e, N, delta):
        super().__init__(name, menv, enc)

        int_type = msat_get_integer_type(menv)
        real_type = msat_get_rational_type(menv)

        loc_symbs, locs, x_locs = self._enum("l", 4)
        evt_symbs, evts, x_evts = self._enum("evt", 5)
        z, x_z = self._symb("z", real_type)
        cnt, x_cnt = self._symb("cnt", int_type)

        self.symb2next = {z: x_z, cnt: x_cnt}
        for s, x_s in chain(loc_symbs, evt_symbs):
            assert s not in self.symb2next
            self.symb2next[s] = x_s

        self.evt_stutter = evts[0]
        self.evt_approach = evts[1]
        self.evt_exit = evts[2]
        self.evt_lower = evts[3]
        self.evt_rise = evts[4]
        x_evt_stutter = x_evts[0]
        x_evt_approach = x_evts[1]
        x_evt_exit = x_evts[2]
        x_evt_lower = x_evts[3]
        x_evt_rise = x_evts[4]

        self.c0 = locs[0]
        self.c1 = locs[1]
        self.c2 = locs[2]
        self.c3 = locs[3]
        self.x_c0 = x_locs[0]
        self.x_c1 = x_locs[1]
        self.x_c2 = x_locs[2]
        self.x_c3 = x_locs[3]

        same_loc = msat_make_iff(menv, loc_symbs[0][1], loc_symbs[0][0])
        for s, x_s in loc_symbs[1:]:
            same_loc = msat_make_and(menv, same_loc,
                                     msat_make_iff(menv, x_s, s))

        nums = [msat_make_number(menv, str(i)) for i in range(N + 1)]
        N = nums[-1]

        # l = c0 & z = 0
        self.init = msat_make_and(menv, self.c0,
                                  msat_make_equal(menv, z, nums[0]))
        # bound l
        bound_l = msat_make_or(menv,
                               msat_make_or(menv, self.c0, self.c1),
                               msat_make_or(menv, self.c2, self.c3))
        self.init = msat_make_and(menv, self.init, bound_l)
        x_bound_l = msat_make_or(menv,
                                 msat_make_or(menv, self.x_c0, self.x_c1),
                                 msat_make_or(menv, self.x_c2, self.x_c3))
        self.trans = x_bound_l

        # bound evt
        bound_evt = msat_make_or(
            menv,
            msat_make_or(menv, self.evt_stutter,
                         self.evt_approach),
            msat_make_or(menv, self.evt_exit,
                         msat_make_or(menv, self.evt_lower,
                                      self.evt_rise)))
        self.init = msat_make_and(menv, self.init, bound_evt)
        x_bound_evt = msat_make_or(
            menv,
            msat_make_or(menv, x_evt_stutter,
                         x_evt_approach),
            msat_make_or(menv, x_evt_exit,
                         msat_make_or(menv, x_evt_lower,
                                      x_evt_rise)))
        self.trans = msat_make_and(menv, self.trans, x_bound_evt)

        # bound cnt
        bound_cnt = msat_make_equal(menv, cnt, nums[0])
        x_bound_cnt = msat_make_equal(menv, x_cnt, nums[0])
        for i in nums[1:]:
            bound_cnt = msat_make_or(menv, bound_cnt,
                                     msat_make_equal(menv, cnt, i))
            x_bound_cnt = msat_make_or(menv, x_bound_cnt,
                                       msat_make_equal(menv, x_cnt, i))
        self.init = msat_make_and(menv, self.init, bound_cnt)
        self.trans = msat_make_and(menv, self.trans, x_bound_cnt)

        # invars: (l = c1 | l = c3) -> (z <= e)
        lhs = msat_make_or(menv, self.c1, self.c3)
        rhs = msat_make_leq(menv, z, e)
        self.init = msat_make_and(menv, self.init,
                                  msat_make_impl(menv, lhs, rhs))
        # invars: (l = c1 | l = c3) -> (z <= e)
        lhs = msat_make_or(menv, self.x_c1, self.x_c3)
        rhs = msat_make_leq(menv, x_z, e)
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))

        # delta > 0 | stutter -> z' = z + delta & l' = l & cnt' = cnt
        lhs = msat_make_or(menv, msat_make_gt(menv, delta, nums[0]),
                           self.evt_stutter)
        rhs = msat_make_and(
            menv,
            msat_make_and(menv,
                          msat_make_equal(menv, x_z,
                                          msat_make_plus(menv, z, delta)),
                          same_loc),
            msat_make_equal(menv, x_cnt, cnt))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))

        disc_t = msat_make_and(menv, msat_make_equal(menv, delta, nums[0]),
                               msat_make_not(menv, self.evt_stutter))

        # (l = c0) -> (l' = c1 & evt_approach & z' = 0 & cnt' = 1)
        lhs = msat_make_and(menv, disc_t, self.c0)
        rhs = msat_make_and(menv,
                            msat_make_and(menv, self.x_c1,
                                          self.evt_approach),
                            msat_make_and(menv,
                                          msat_make_equal(menv, x_z, nums[0]),
                                          msat_make_equal(menv, x_cnt,
                                                          nums[1])))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        # (l = c1) -> ((l' = c1 | l' = c2) & z' = z)
        lhs = msat_make_and(menv, disc_t, self.c1)
        rhs = msat_make_and(menv,
                            msat_make_equal(menv, x_z, z),
                            msat_make_or(menv, self.x_c1, self.x_c2))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        # (l = c1 & l' = c1) -> ((evt_approach & cnt' = cnt + 1) |
        # (evt_exit & cnt' = cnt - 1))
        lhs = msat_make_and(menv, disc_t,
                            msat_make_and(menv, self.c1, self.x_c1))
        dec_cnt = msat_make_equal(menv, x_cnt,
                                  msat_make_minus(menv, cnt, nums[1]))
        inc_cnt = msat_make_equal(menv, x_cnt,
                                  msat_make_plus(menv, cnt, nums[1]))
        rhs = msat_make_or(menv,
                           msat_make_and(menv, self.evt_approach, inc_cnt),
                           msat_make_and(menv, self.evt_exit, dec_cnt))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        # (l = c1 & l' = c2) -> (evt_lower & z = e & cnt' = cnt)
        lhs = msat_make_and(menv, disc_t,
                            msat_make_and(menv, self.c1, self.x_c2))
        rhs = msat_make_and(menv, self.evt_lower,
                            msat_make_and(menv,
                                          msat_make_equal(menv, z, e),
                                          msat_make_equal(menv, x_cnt, cnt)))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        # (l = c2) -> (l' = c2 | l' = c3)
        lhs = msat_make_and(menv, disc_t, self.c2)
        rhs = msat_make_or(menv, self.x_c2, self.x_c3)
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        # l = c2 & l' = c2) -> (z' = z & ((cnt > 1 & evt_exit & cnt' = cnt - 1) |
        # (evt_approach & cnt' = cnt + 1)))
        lhs = msat_make_and(menv, disc_t,
                            msat_make_and(menv, self.c2, self.x_c2))
        disj0 = msat_make_and(menv,
                              msat_make_gt(menv, cnt, nums[1]),
                              msat_make_and(menv, self.evt_exit,
                                            dec_cnt))
        rhs = msat_make_and(menv,
                            msat_make_equal(menv, x_z, z),
                            msat_make_or(menv, disj0,
                                         msat_make_and(menv, self.evt_approach,
                                                       inc_cnt)))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        # (l = c2 & l' = c3) -> (cnt = 1 & evt_exit & z' = 0 & cnt' = 0)
        lhs = msat_make_and(menv, disc_t,
                            msat_make_and(menv, self.c2, self.x_c3))
        rhs = msat_make_and(menv,
                            msat_make_and(menv,
                                          msat_make_equal(menv, cnt, nums[1]),
                                          self.evt_exit),
                            msat_make_and(menv,
                                          msat_make_equal(menv, x_z, nums[0]),
                                          msat_make_equal(menv, x_cnt,
                                                          nums[0])))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        # (l = c3) -> ((l' = c2 | l' = c0) & z' = z)
        lhs = msat_make_and(menv, disc_t, self.c3)
        rhs = msat_make_and(menv,
                            msat_make_equal(menv, x_z, z),
                            msat_make_or(menv, self.x_c2, self.x_c0))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        # (l = c3 & l' = c2) -> (z <= e & evt_approach & cnt' = cnt + 1)
        lhs = msat_make_and(menv, disc_t,
                            msat_make_and(menv, self.c3, self.x_c2))
        rhs = msat_make_and(menv, inc_cnt,
                            msat_make_and(menv,
                                          msat_make_leq(menv, z, e),
                                          self.evt_approach))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        # (l = c3 & l' = c0) -> (z <= e & evt_rise & cnt' = cnt)
        lhs = msat_make_and(menv, disc_t,
                            msat_make_and(menv, self.c3, self.x_c0))
        rhs = msat_make_and(menv,
                            msat_make_equal(menv, x_cnt, cnt),
                            msat_make_and(menv, self.evt_rise,
                                          msat_make_leq(menv, z, e)))
