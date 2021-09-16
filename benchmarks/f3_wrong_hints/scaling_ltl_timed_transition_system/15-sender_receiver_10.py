from typing import FrozenSet
from collections import Iterable
from math import log, ceil

from mathsat import msat_term, msat_env
from mathsat import msat_make_constant, msat_declare_function
from mathsat import msat_get_integer_type, msat_get_rational_type,     msat_get_bool_type
from mathsat import msat_make_and, msat_make_not, msat_make_or, msat_make_iff
from mathsat import msat_make_leq, msat_make_equal, msat_make_true
from mathsat import msat_make_number, msat_make_plus, msat_make_times

from pysmt.environment import Environment as PysmtEnv
import pysmt.typing as types

from ltl.ltl import TermMap, LTLEncoder
from utils import name_next, symb_to_next
from hint import Hint, Location

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
    int_type = msat_get_integer_type(menv)
    real_type = msat_get_rational_type(menv)
    r2s, x_r2s = decl_consts(menv, "r2s", int_type)
    s2r, x_s2r = decl_consts(menv, "s2r", int_type)
    delta, x_delta = decl_consts(menv, delta_name, real_type)
    sender = Sender("s", menv, enc, r2s, x_r2s, s2r, x_s2r, delta)
    receiver = Receiver("r", menv, enc, s2r, x_s2r, r2s, x_r2s, delta)

    curr2next = {r2s: x_r2s, s2r: x_s2r, delta: x_delta}
    for comp in [sender, receiver]:
        for s, x_s in comp.symb2next.items():
            curr2next[s] = x_s

    zero = msat_make_number(menv, "0")
    init = msat_make_and(menv, receiver.init, sender.init)
    trans = msat_make_and(menv, receiver.trans, sender.trans)

    # invar delta >= 0
    init = msat_make_and(menv, init,
                         msat_make_geq(menv, delta, zero))
    trans = msat_make_and(menv, trans,
                          msat_make_geq(menv, x_delta, zero))

    # delta > 0 -> (r2s' = r2s & s2r' = s2r)
    lhs = msat_make_gt(menv, delta, zero)
    rhs = msat_make_and(menv,
                        msat_make_equal(menv, x_r2s, r2s),
                        msat_make_equal(menv, x_s2r, s2r))
    trans = msat_make_and(menv, trans,
                          msat_make_impl(menv, lhs, rhs))

    # (G F !s.stutter) -> G (s.wait_ack -> F s.send)
    lhs = enc.make_G(enc.make_F(msat_make_not(menv, sender.stutter)))
    rhs = enc.make_G(msat_make_impl(menv, sender.wait_ack,
                                    enc.make_F(sender.send)))
    ltl = msat_make_impl(menv, lhs, rhs)
    return TermMap(curr2next), init, trans, ltl


class Module:
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
        c_name = "{}_{}".format(self.name, v_name)
        return make_enum(self.menv, c_name, enum_size)


class Sender(Module):
    def __init__(self, name: str, menv: msat_env, enc: LTLEncoder,
                 in_c, x_in_c, out_c, x_out_c, delta):
        super().__init__(name, menv, enc)

        bool_type = msat_get_bool_type(menv)
        int_type = msat_get_integer_type(menv)
        real_type = msat_get_rational_type(menv)
        loc, x_loc = self._symb("l", bool_type)
        evt, x_evt = self._symb("evt", bool_type)
        msg_id, x_msg_id = self._symb("msg_id", int_type)
        timeout, x_timeout = self._symb("timeout", real_type)
        c, x_c = self._symb("c", real_type)

        self.move = evt
        self.stutter = msat_make_not(menv, evt)
        self.x_move = x_evt
        self.x_stutter = msat_make_not(menv, x_evt)

        self.send = loc
        self.wait_ack = msat_make_not(menv, loc)
        self.x_send = x_loc
        self.x_wait_ack = msat_make_not(menv, x_loc)

        self.symb2next = {loc: x_loc, evt: x_evt, msg_id: x_msg_id,
                          timeout: x_timeout, c: x_c}

        zero = msat_make_number(menv, "0")
        one = msat_make_number(menv, "1")
        base_timeout = one

        # send & c = 0 & msg_id = 0
        self.init = msat_make_and(menv,
                                  msat_make_and(menv, self.send,
                                                msat_make_equal(menv, c,
                                                                zero)),
                                  msat_make_equal(menv, msg_id, zero))
        # invar: wait_ack -> c <= timeout
        self.init = msat_make_and(
            menv, self.init,
            msat_make_impl(menv, self.wait_ack,
                           msat_make_leq(menv, c, timeout)))
        self.trans = msat_make_impl(menv, self.x_wait_ack,
                                    msat_make_leq(menv, x_c, x_timeout))

        # delta > 0 | stutter -> l' = l & msg_id' = msg_id & timeout' = timeout &
        # c' = c + delta & out_c' = out_c
        lhs = msat_make_or(menv, msat_make_gt(menv, delta, zero), self.stutter)
        rhs = msat_make_and(
            menv,
            msat_make_and(menv,
                          msat_make_iff(menv, x_loc, loc),
                          msat_make_equal(menv, x_msg_id, msg_id)),
            msat_make_and(menv,
                          msat_make_equal(menv, x_timeout, timeout),
                          msat_make_equal(menv, x_c,
                                          msat_make_plus(menv, c, delta))))
        rhs = msat_make_and(menv, rhs,
                            msat_make_equal(menv, x_out_c, out_c))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))

        disc_t = msat_make_and(menv, self.move,
                               msat_make_equal(menv, delta, zero))
        # (send & send') ->
        # (msg_id' = msg_id & timeout' = base_timeout & c' = 0 & out_c' = out_c)
        lhs = msat_make_and(menv, disc_t,
                            msat_make_and(menv, self.send, self.x_send))
        rhs = msat_make_and(
            menv,
            msat_make_and(menv,
                          msat_make_equal(menv, x_msg_id, msg_id),
                          msat_make_equal(menv, x_timeout, base_timeout)),
            msat_make_and(menv,
                          msat_make_equal(menv, x_c, zero),
                          msat_make_equal(menv, x_out_c, out_c)))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        # (send & wait_ack') ->
        # (msg_id' = msg_id + 1 & timeout' = base_timeout & c' = 0 & out_c' = out_c)
        lhs = msat_make_and(menv, disc_t,
                            msat_make_and(menv, self.send, self.x_wait_ack))
        rhs = msat_make_and(
            menv,
            msat_make_and(menv,
                          msat_make_equal(menv, x_msg_id,
                                          msat_make_plus(menv, msg_id, one)),
                          msat_make_equal(menv, x_timeout, base_timeout)),
            msat_make_and(menv,
                          msat_make_equal(menv, x_c, zero),
                          msat_make_equal(menv, x_out_c, out_c)))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        # (wait_ack) -> (c' = 0 & out_c' = out_c &
        # (wait_ack' <-> (in_c != msg_id & c > timeout))
        lhs = msat_make_and(menv, disc_t, self.wait_ack)
        rhs_iff = msat_make_and(menv,
                                msat_make_not(menv,
                                              msat_make_equal(menv, in_c,
                                                              msg_id)),
                                msat_make_geq(menv, c, timeout))
        rhs_iff = msat_make_iff(menv, self.x_wait_ack, rhs_iff)
        rhs = msat_make_and(menv,
                            msat_make_and(menv,
                                          msat_make_equal(menv, x_c, zero),
                                          msat_make_equal(menv, x_out_c,
                                                          out_c)),
                            rhs_iff)
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        # (wait_ack & wait_ack') -> (timeout' > timeout)
        lhs = msat_make_and(menv, disc_t,
                            msat_make_and(menv, self.wait_ack,
                                          self.x_wait_ack))
        rhs = msat_make_gt(menv, x_timeout, timeout)
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        # (wait_ack) -> (send' <-> (in_c = msg_id & c < timeout))
        lhs = msat_make_and(menv, disc_t, self.wait_ack)
        rhs = msat_make_iff(menv, self.x_send,
                            msat_make_and(menv,
                                          msat_make_equal(menv, in_c, msg_id),
                                          msat_make_lt(menv, c, timeout)))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        # (wait_ack & send') -> (timeout' = base_timeout)
        lhs = msat_make_and(menv, disc_t,
                            msat_make_and(menv, self.wait_ack, self.x_send))
        rhs = msat_make_equal(menv, x_timeout, base_timeout)
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))


class Receiver(Module):
    def __init__(self, name: str, menv: msat_env, enc: LTLEncoder,
                 in_c, x_in_c, out_c, x_out_c, delta):
        super().__init__(name, menv, enc)

        bool_type = msat_get_bool_type(menv)
        loc, x_loc = self._symb("l", bool_type)

        self.wait = loc
        self.work = msat_make_not(menv, loc)
        self.x_wait = x_loc
        self.x_work = msat_make_not(menv, x_loc)

        self.symb2next = {loc: x_loc}

        zero = msat_make_number(menv, "0")
        # wait
        self.init = self.wait

        # delta > 0 -> loc' = loc & out_c' = out_c
        lhs = msat_make_gt(menv, delta, zero)
        rhs = msat_make_and(menv,
                            msat_make_iff(menv, x_loc, loc),
                            msat_make_equal(menv, x_out_c, out_c))
        self.trans = msat_make_impl(menv, lhs, rhs)

        disc_t = msat_make_equal(menv, delta, zero)
        # wait -> (wait' <-> in_c = out_c)
        lhs = msat_make_and(menv, disc_t, self.wait)
        rhs = msat_make_iff(menv, self.x_wait,
                            msat_make_equal(menv, in_c, out_c))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        # (wait & wait') -> (out_c' = out_c)
        lhs = msat_make_and(menv, disc_t,
                            msat_make_and(menv, self.wait, self.x_wait))
        rhs = msat_make_equal(menv, x_out_c, out_c)
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        # (wait & work') -> out_c' = in_c
        lhs = msat_make_and(menv, disc_t,
                            msat_make_and(menv, self.wait, self.x_work))
        rhs = msat_make_equal(menv, x_out_c, in_c)
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        # work -> out_c' = out_c
        lhs = msat_make_and(menv, disc_t, self.work)
        rhs = msat_make_equal(menv, x_out_c, out_c)
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))


def hints(env: PysmtEnv) -> FrozenSet[Hint]:
    assert isinstance(env, PysmtEnv)

    mgr = env.formula_manager
    delta = mgr.Symbol(delta_name, types.REAL)
    r2s = mgr.Symbol("r2s", types.INT)
    s2r = mgr.Symbol("r2s", types.INT)
    s_l = mgr.Symbol("s_l", types.BOOL)
    s_evt = mgr.Symbol("s_evt", types.BOOL)
    s_msg_id = mgr.Symbol("s_msg_id", types.INT)
    s_timeout = mgr.Symbol("s_timeout", types.REAL)
    s_c = mgr.Symbol("s_c", types.REAL)
    r_l = mgr.Symbol("r_l", types.BOOL)
    symbs = frozenset([delta, r2s, s2r, s_l, s_evt, s_msg_id, s_timeout, s_c,
                       r_l])

    x_delta = symb_to_next(mgr, delta)
    x_r2s = symb_to_next(mgr, r2s)
    x_s2r = symb_to_next(mgr, s2r)
    x_s_l = symb_to_next(mgr, s_l)
    x_s_evt = symb_to_next(mgr, s_evt)
    x_s_msg_id = symb_to_next(mgr, s_msg_id)
    x_s_timeout = symb_to_next(mgr, s_timeout)
    x_s_c = symb_to_next(mgr, s_c)
    x_r_l = symb_to_next(mgr, r_l)

    res = []

    r0 = mgr.Real(0)
    r1 = mgr.Real(1)
    i0 = mgr.Int(0)
    i1 = mgr.Int(1)

    loc0 = Location(env, mgr.Equals(delta, r0))
    loc0.set_progress(0, mgr.Equals(x_delta, r0))
    hint = Hint("h_delta0", env, frozenset([delta]), symbs)
    hint.set_locs([loc0])
    res.append(hint)


    loc0 = Location(env, mgr.Equals(s2r, i0))
    loc0.set_progress(0, mgr.Equals(x_s2r, i0))
    hint = Hint("h_s2r0", env, frozenset([s2r]), symbs)
    hint.set_locs([loc0])
    res.append(hint)


    loc0 = Location(env, s_evt)
    loc0.set_progress(0, x_s_evt)
    hint = Hint("h_s_evt0", env, frozenset([s_evt]), symbs)
    hint.set_locs([loc0])
    res.append(hint)


    loc0 = Location(env, mgr.Equals(s_msg_id, i0))
    loc0.set_progress(0, mgr.Equals(x_s_msg_id, i0))
    hint = Hint("h_s_msg_id0", env, frozenset([s_msg_id]), symbs)
    hint.set_locs([loc0])
    res.append(hint)


    loc0 = Location(env, mgr.Equals(s_c, r0))
    loc0.set_progress(0, mgr.Equals(x_s_c, r0))
    hint = Hint("h_s_c0", env, frozenset([s_c]), symbs)
    hint.set_locs([loc0])
    res.append(hint)


    loc0 = Location(env, r_l)
    loc0.set_progress(0, x_r_l)
    hint = Hint("h_r_l0", env, frozenset([r_l]), symbs)
    hint.set_locs([loc0])
    res.append(hint)


    loc0 = Location(env, mgr.GE(s2r, i0))
    loc0.set_progress(0, mgr.Equals(x_s2r, i1))
    hint = Hint("h_s2r1", env, frozenset([s2r]), symbs)
    hint.set_locs([loc0])
    res.append(hint)


    loc0 = Location(env, mgr.GE(r2s, i0))
    loc0.set_progress(0, mgr.Equals(x_r2s, i1))
    hint = Hint("h_r2s1", env, frozenset([r2s]), symbs)
    hint.set_locs([loc0])
    res.append(hint)


    loc0 = Location(env, s_l)
    loc0.set_progress(1, mgr.Not(x_s_l))
    loc1 = Location(env, mgr.Not(s_l))
    loc1.set_progress(0, x_s_l)
    hint = Hint("h_s_l1", env, frozenset([s_l]), symbs)
    hint.set_locs([loc0, loc1])
    res.append(hint)


    loc0 = Location(env, s_evt)
    loc0.set_progress(1, mgr.Not(x_s_evt))
    loc1 = Location(env, mgr.Not(s_evt))
    loc1.set_progress(0, x_s_evt)
    hint = Hint("h_s_evt1", env, frozenset([s_evt]), symbs)
    hint.set_locs([loc0, loc1])
    res.append(hint)


    loc0 = Location(env, mgr.GE(s_msg_id, i0))
    loc0.set_progress(0, mgr.Equals(x_s_msg_id, mgr.Plus(s_msg_id, i1)))
    hint = Hint("h_s_msg_id1", env, frozenset([s_msg_id]), symbs)
    hint.set_locs([loc0])
    res.append(hint)


    loc0 = Location(env, mgr.GE(s_timeout, r0))
    loc0.set_progress(0, mgr.Equals(x_s_timeout, mgr.Plus(s_timeout, r1)))
    hint = Hint("h_s_timeout1", env, frozenset([s_timeout]), symbs)
    hint.set_locs([loc0])
    res.append(hint)


    loc0 = Location(env, r_l)
    loc0.set_progress(1, mgr.Not(x_r_l))
    loc1 = Location(env, mgr.Not(r_l))
    loc1.set_progress(0, x_r_l)
    hint = Hint("h_r_l1", env, frozenset([r_l]), symbs)
    hint.set_locs([loc0, loc1])
    res.append(hint)


    loc0 = Location(env, mgr.GE(delta, r0))
    loc0.set_progress(0, mgr.Equals(x_delta, mgr.Plus(delta, r1)))
    hint = Hint("h_delta2", env, frozenset([delta]), symbs)
    hint.set_locs([loc0])
    res.append(hint)


    loc0 = Location(env, mgr.GE(s2r, i0))
    loc0.set_progress(0, mgr.Equals(x_s2r, mgr.Plus(s2r, i1)))
    hint = Hint("h_s2r2", env, frozenset([s2r]), symbs)
    hint.set_locs([loc0])
    res.append(hint)

    return frozenset(res)
