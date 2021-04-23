from collections import Iterable
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

num_procs = 19
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
    int_type = msat_get_integer_type(menv)
    bool_type = msat_get_bool_type(menv)

    delta, x_delta = decl_consts(menv, delta_name, real_type)
    v1, x_v1 = decl_consts(menv, "v1", int_type)
    v2, x_v2 = decl_consts(menv, "v2", bool_type)

    curr2next = {delta: x_delta, v1: x_v1, v2: x_v2}

    T = msat_make_number(menv, "16")

    procs = [P("p{}".format(idx), menv, enc,
               msat_make_number(menv, str(idx + 1)), v1, x_v1, v2, x_v2, T,
               delta)
             for idx in range(num_procs)]

    for p in procs:
        for s, x_s in p.symb2next.items():
            assert s not in curr2next.keys()
            curr2next[s] = x_s

    zero = msat_make_number(menv, "0")
    one = msat_make_number(menv, "1")

    init = msat_make_geq(menv, delta, zero)
    # bound v1
    bound_v1 = msat_make_equal(menv, v1, zero)
    x_bound_v1 = msat_make_equal(menv, x_v1, zero)
    for idx in range(1, num_procs + 1):
        num = msat_make_number(menv, str(idx))
        bound_v1 = msat_make_or(menv, bound_v1,
                                msat_make_equal(menv, v1, num))
        x_bound_v1 = msat_make_or(menv, x_bound_v1,
                                  msat_make_equal(menv, x_v1, num))
    init = msat_make_and(menv, init, bound_v1)
    trans = x_bound_v1

    trans = msat_make_and(menv, trans, msat_make_geq(menv, x_delta, zero))
    # delta > 0 -> v1' = v1 & v2' <-> v2
    curr = msat_make_impl(menv, msat_make_gt(menv, delta, zero),
                          msat_make_and(menv,
                                        msat_make_equal(menv, x_v1, v1),
                                        msat_make_iff(menv, x_v2, v2)))
    trans = msat_make_and(menv, curr, trans)

    for p in procs:
        init = msat_make_and(menv, init, p.init)
        trans = msat_make_and(menv, trans, p.trans)

    d_eq_0 = msat_make_equal(menv, delta, zero)

    # !(p0.evt_stutter & p1.evt_stutter)
    all_stutter = procs[0].evt_stutter
    for p in procs[1:]:
        all_stutter = msat_make_and(menv, all_stutter, p.evt_stutter)
    trans = msat_make_and(menv, trans,
                          msat_make_impl(menv, d_eq_0,
                                         msat_make_not(menv, all_stutter)))

    # (G F v1 = 1) -> (G F p0.CS7)
    ltl = msat_make_impl(
        menv,
        enc.make_G(enc.make_F(msat_make_equal(menv, v1, one))),
        enc.make_G(enc.make_F(procs[0].CS7)))
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


class P(Module):
    """Process module"""
    def __init__(self, name: str, menv: msat_env, enc: LTLEncoder,
                 pid, v1, x_v1, v2, x_v2, T, delta):
        super().__init__(name, menv, enc)

        # int_type = msat_get_integer_type(menv)
        real_type = msat_get_rational_type(menv)
        bool_type = msat_get_bool_type(menv)

        # loc, x_loc = self._symb("l", int_type)
        loc_symbs, locs, x_locs = self._enum("l", 9)
        c, x_c = self._symb("c", real_type)
        evt, x_evt = self._symb("evt", bool_type)

        self.evt_move = evt
        self.evt_stutter = msat_make_not(menv, evt)

        self.symb2next = {c: x_c, evt: x_evt}
        for s, x_s in loc_symbs:
            assert s not in self.symb2next
            self.symb2next[s] = x_s

        nums = [msat_make_number(menv, str(n))
                for n in range(9)]

        self.L1 = locs[0]
        self.L2 = locs[1]
        self.L3 = locs[2]
        self.L4 = locs[3]
        self.L5 = locs[4]
        self.L6 = locs[5]
        self.CS7 = locs[6]
        self.L8 = locs[7]
        self.L9 = locs[8]
        self.x_L1 = x_locs[0]
        self.x_L2 = x_locs[1]
        self.x_L3 = x_locs[2]
        self.x_L4 = x_locs[3]
        self.x_L5 = x_locs[4]
        self.x_L6 = x_locs[5]
        self.x_CS7 = x_locs[6]
        self.x_L8 = x_locs[7]
        self.x_L9 = x_locs[8]

        # l = L1 & c = 0
        self.init = msat_make_and(menv, self.L1,
                                  msat_make_equal(menv, c, nums[0]))
        # bound l
        bound_l = locs[0]
        x_bound_l = x_locs[0]
        for loc, x_loc in zip(locs[1:], x_locs[1:]):
            bound_l = msat_make_or(menv, bound_l, loc)
            x_bound_l = msat_make_or(menv, x_bound_l, x_loc)

        same_loc = msat_make_iff(menv, loc_symbs[0][1], loc_symbs[0][0])
        for s, x_s in loc_symbs[1:]:
            same_loc = msat_make_and(menv, same_loc,
                                     msat_make_iff(menv, x_s, s))

        self.init = msat_make_and(menv, self.init, bound_l)
        self.trans = x_bound_l
        # invars
        lhs = msat_make_or(menv,
                           msat_make_or(menv, self.L2, self.L5),
                           msat_make_or(menv, self.L8, self.L9))
        rhs = msat_make_leq(menv, c, T)
        self.init = msat_make_and(menv, self.init,
                                  msat_make_impl(menv, lhs, rhs))
        # invars
        lhs = msat_make_or(menv,
                           msat_make_or(menv, self.x_L2, self.x_L5),
                           msat_make_or(menv, self.x_L8, self.x_L9))
        rhs = msat_make_leq(menv, x_c, T)
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))

        # delta > 0 -> c' = c + delta & l' = l
        self.trans = msat_make_and(
            menv, self.trans,
            msat_make_impl(
                menv, msat_make_gt(menv, delta, nums[0]),
                msat_make_and(menv,
                              msat_make_equal(menv, x_c,
                                              msat_make_plus(menv, c, delta)),
                              same_loc)))

        # stutter -> l' = l & c' = c + delta
        lhs = self.evt_stutter
        rhs = msat_make_and(menv, same_loc,
                            msat_make_equal(menv, x_c,
                                            msat_make_plus(menv, c, delta)))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))

        disc_t = msat_make_and(menv, msat_make_equal(menv, delta, nums[0]),
                               self.evt_move)
        # (l = L1) -> (v1 = 0 & l' = L2 & c' = 0 & (v2' <-> v2) & v1' = v1)
        lhs = msat_make_and(menv, disc_t, self.L1)
        rhs = msat_make_and(menv,
                            msat_make_and(menv,
                                          msat_make_equal(menv, v1, nums[0]),
                                          self.x_L2),
                            msat_make_and(menv,
                                          msat_make_equal(menv, x_c, nums[0]),
                                          msat_make_iff(menv, x_v2, v2)))
        rhs = msat_make_and(menv, rhs,
                            msat_make_equal(menv, x_v1, v1))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        # (l = L2) -> (v1' = id & l' = L3 & c' = 0 & (v2' <-> v2))
        lhs = msat_make_and(menv, disc_t, self.L2)
        rhs = msat_make_and(menv,
                            msat_make_and(menv, self.x_L3,
                                          msat_make_equal(menv, x_v1, pid)),
                            msat_make_and(menv,
                                          msat_make_equal(menv, x_c, nums[0]),
                                          msat_make_iff(menv, x_v2, v2)))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        # (l = L3) -> ((l' = L1 | l' = L4) & c' = c & (v2' <-> v2) & v1' = v1)
        lhs = msat_make_and(menv, disc_t, self.L3)
        rhs = msat_make_and(
            menv,
            msat_make_and(menv,
                          msat_make_or(menv, self.x_L1, self.x_L4),
                          msat_make_equal(menv, x_c, c)),
            msat_make_and(menv,
                          msat_make_iff(menv, x_v2, v2),
                          msat_make_equal(menv, x_v1, v1)))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        # (l = L3 & l' = L1) -> (v1 != id)
        lhs = msat_make_and(menv, disc_t, self.L3)
        lhs = msat_make_and(menv, lhs, self.x_L1)
        rhs = msat_make_not(menv, msat_make_equal(menv, v1, pid))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        # (l = L3 & l' = L4) -> (v1 = id & c > _T)
        lhs = msat_make_and(menv, disc_t, self.L3)
        lhs = msat_make_and(menv, lhs, self.x_L4)
        rhs = msat_make_and(menv, msat_make_equal(menv, v1, pid),
                            msat_make_gt(menv, c, T))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        # (l = L4) -> ((l' = L1 | l' = L5) & (v2' <-> v2) & v1' = v1)
        lhs = msat_make_and(menv, disc_t, self.L4)
        rhs = msat_make_and(menv,
                            msat_make_or(menv, self.x_L1, self.x_L5),
                            msat_make_and(menv,
                                          msat_make_iff(menv, x_v2, v2),
                                          msat_make_equal(menv, x_v1, v1)))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        # (l = L4 & l' = L1) -> (v2 & c' = c)
        lhs = msat_make_and(menv, disc_t,
                            msat_make_and(menv, self.L4, self.x_L1))
        rhs = msat_make_and(menv, v2, msat_make_equal(menv, x_c, c))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        # (l = L4 & l' = L5) -> (!v2 & c' = 0)
        lhs = msat_make_and(menv, disc_t,
                            msat_make_and(menv, self.L4, self.x_L5))
        rhs = msat_make_and(menv,
                            msat_make_not(menv, v2),
                            msat_make_equal(menv, x_c, nums[0]))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        # (l = L5) -> (l' = L6 & v2' & c' = 0 & v1' = v1)
        lhs = msat_make_and(menv, disc_t, self.L5)
        rhs = msat_make_and(menv,
                            msat_make_and(menv, self.x_L6, x_v2),
                            msat_make_and(menv,
                                          msat_make_equal(menv, x_c, nums[0]),
                                          msat_make_equal(menv, x_v1, v1)))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        # (l = L6) -> ((l' = L1 | l' = CS7) & c' = c & (v2' <-> v2) & v1' = v1)
        lhs = msat_make_and(menv, disc_t, self.L6)
        rhs = msat_make_and(menv,
                            msat_make_and(menv,
                                          msat_make_or(menv, self.x_L1,
                                                       self.x_CS7),
                                          msat_make_equal(menv, x_c, c)),
                            msat_make_and(menv,
                                          msat_make_iff(menv, x_v2, v2),
                                          msat_make_equal(menv, x_v1, v1)))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        # (l = L6 & l' = L1) -> (v1 != id)
        lhs = msat_make_and(menv, disc_t,
                            msat_make_and(menv, self.L6, self.x_L1))
        rhs = msat_make_not(menv, msat_make_equal(menv, v1, pid))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        # (l = L6 & l' = CS7) -> (v1 = id)
        lhs = msat_make_and(menv, disc_t,
                            msat_make_and(menv, self.L6, self.x_CS7))
        rhs = msat_make_equal(menv, v1, pid)
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        # (l = CS7) -> (l' = L8 & c' = 0 & (v2' <-> v2) & v1' = v1)
        lhs = msat_make_and(menv, disc_t, self.CS7)
        rhs = msat_make_and(menv,
                            msat_make_and(menv, self.x_L8,
                                          msat_make_equal(menv, x_c, nums[0])),
                            msat_make_and(menv,
                                          msat_make_iff(menv, x_v2, v2),
                                          msat_make_equal(menv, x_v1, v1)))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        # (l = L8) -> (l' = L9 & !v2' & c' = 0 & v1' = v1)
        lhs = msat_make_and(menv, disc_t, self.L8)
        rhs = msat_make_and(menv,
                            msat_make_and(menv, self.x_L9,
                                          msat_make_not(menv, x_v2)),
                            msat_make_and(menv,
                                          msat_make_equal(menv, x_c, nums[0]),
                                          msat_make_equal(menv, x_v1, v1)))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        # (l = L9) -> (l' = L1 & v1' = 0 & (v2' <-> v2) & c' = c)
        lhs = msat_make_and(menv, disc_t, self.L9)
        rhs = msat_make_and(
            menv,
            msat_make_and(menv, self.x_L1,
                          msat_make_equal(menv, x_v1, nums[0])),
            msat_make_and(menv,
                          msat_make_iff(menv, x_v2, v2),
                          msat_make_equal(menv, x_c, c)))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
