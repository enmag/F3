from typing import Iterable, Tuple
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

num_procs = 29
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
    int_type = msat_get_integer_type(menv)

    delta, x_delta = decl_consts(menv, delta_name, real_type)
    s_id, x_id = decl_consts(menv, "id", int_type)
    turn, x_turn = decl_consts(menv, "turn", int_type)

    curr2next = {delta: x_delta, s_id: x_id, turn: x_turn}

    procs = [P("p{}".format(idx), menv, enc,
               msat_make_number(menv, str(idx + 1)), s_id, x_id, turn, delta)
             for idx in range(num_procs)]

    for p in procs:
        for s, x_s in p.symb2next.items():
            assert s not in curr2next.keys()
            curr2next[s] = x_s

    zero = msat_make_number(menv, "0")
    one = msat_make_number(menv, "1")

    init = msat_make_geq(menv, delta, zero)
    # bound id
    bound_id = msat_make_equal(menv, s_id, zero)
    x_bound_id = msat_make_equal(menv, x_id, zero)
    for idx in range(1, num_procs + 1):
        num = msat_make_number(menv, str(idx))
        bound_id = msat_make_or(menv, bound_id,
                                msat_make_equal(menv, s_id, num))
        x_bound_id = msat_make_or(menv, x_bound_id,
                                  msat_make_equal(menv, x_id, num))
    init = msat_make_and(menv, init, bound_id)
    trans = bound_id
    # bound turn
    bound_turn = msat_make_equal(menv, turn, one)
    x_bound_turn = msat_make_equal(menv, x_turn, one)
    for idx in range(2, num_procs + 1):
        num = msat_make_number(menv, str(idx))
        bound_turn = msat_make_or(menv, bound_turn,
                                  msat_make_equal(menv, turn, num))
        x_bound_turn = msat_make_or(menv, x_bound_turn,
                                    msat_make_equal(menv, x_turn, num))
    init = msat_make_and(menv, init, bound_turn)
    trans = msat_make_and(menv, trans, x_bound_turn)

    trans = msat_make_and(menv, trans,
                          msat_make_geq(menv, x_delta, zero))

    # delta > 0 -> id' = id & turn' = turn
    curr = msat_make_impl(menv, msat_make_gt(menv, delta, zero),
                          msat_make_and(menv,
                                        msat_make_equal(menv, x_id, s_id),
                                        msat_make_equal(menv, x_turn, turn)))
    trans = msat_make_and(menv, curr, trans)

    for p in procs:
        init = msat_make_and(menv, init, p.init)
        trans = msat_make_and(menv, trans, p.trans)

    init = msat_make_and(menv, init, msat_make_equal(menv, s_id, zero))

    # (G F P0.location = wait) -> (G F P0.location = cs)
    ltl = msat_make_impl(menv,
                         enc.make_G(enc.make_F(procs[0].wait)),
                         enc.make_G(enc.make_F(procs[0].cs)))
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
                 pid, s_id, x_id, turn, delta):
        super().__init__(name, menv, enc)

        # int_type = msat_get_integer_type(menv)
        real_type = msat_get_rational_type(menv)

        # loc, x_loc = self._symb("l", int_type)
        loc_symbs, locs, x_locs = self._enum("l", 4)
        x, x_x = self._symb("x", real_type)

        self.symb2next = {x: x_x}
        for s, x_s in loc_symbs:
            assert s not in self.symb2next
            self.symb2next[s] = x_s

        nums = [msat_make_number(menv, str(n))
                for n in range(4)]

        k = nums[2]

        self.idle = locs[0]
        self.wait = locs[1]
        self.req = locs[2]
        self.cs = locs[3]
        self.x_idle = x_locs[0]
        self.x_wait = x_locs[1]
        self.x_req = x_locs[2]
        self.x_cs = x_locs[3]

        same_loc = msat_make_iff(menv, loc_symbs[0][1], loc_symbs[0][0])
        for s, x_s in loc_symbs[1:]:
            same_loc = msat_make_and(menv, same_loc,
                                     msat_make_iff(menv, x_s, s))

        # l = idle & x = 0
        self.init = msat_make_and(menv, self.idle,
                                  msat_make_equal(menv, x, nums[0]))
        # bound l
        bound_l = msat_make_or(menv,
                               msat_make_or(menv, self.idle, self.wait),
                               msat_make_or(menv, self.req, self.cs))
        self.init = msat_make_and(menv, self.init, bound_l)
        # invars
        self.init = msat_make_and(
            menv, self.init,
            msat_make_impl(menv, self.req, msat_make_leq(menv, x, k)))

        # bound l
        bound_l = msat_make_or(menv,
                               msat_make_or(menv, self.x_idle, self.x_wait),
                               msat_make_or(menv, self.x_req, self.x_cs))
        self.trans = msat_make_and(menv, self.trans, bound_l)
        # invars
        self.trans = msat_make_and(
            menv, self.trans,
            msat_make_impl(menv, self.x_req,
                           msat_make_leq(menv, x_x, k)))

        lhs = msat_make_or(
            menv,
            msat_make_gt(menv, delta, nums[0]),
            msat_make_not(menv, msat_make_equal(menv, turn, pid)))
        rhs = msat_make_and(menv,
                            same_loc,
                            msat_make_equal(menv, x_x,
                                            msat_make_plus(menv, x, delta)))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))

        disc_t = msat_make_and(menv, msat_make_equal(menv, delta, nums[0]),
                               msat_make_equal(menv, turn, pid))
        # (l = idle) ->  l' = req & id = 0 & x' = 0 & id' = id
        lhs = msat_make_and(menv, disc_t, self.idle)
        rhs = msat_make_and(
            menv,
            msat_make_and(menv, self.x_req,
                          msat_make_equal(menv, s_id, nums[0])),
            msat_make_and(menv,
                          msat_make_equal(menv, x_x, nums[0]),
                          msat_make_equal(menv, x_id, s_id)))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        # (l = req)  ->  l' = wait & x <= k & x' = 0 & id' = pid
        lhs = msat_make_and(menv, disc_t, self.req)
        rhs = msat_make_and(
            menv,
            msat_make_and(menv, self.x_wait,
                          msat_make_leq(menv, x, k)),
            msat_make_and(menv,
                          msat_make_equal(menv, x_x, nums[0]),
                          msat_make_equal(menv, x_id, pid)))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        # (l = wait) -> (l' = idle | l' = cs)
        lhs = msat_make_and(menv, disc_t, self.wait)
        rhs = msat_make_or(menv, self.x_idle, self.x_cs)
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        # (l = wait & l' = idle) -> x' = 0 & id' = id & x > k & id != pid
        lhs = msat_make_and(menv, disc_t,
                            msat_make_and(menv, self.wait, self.x_idle))
        rhs = msat_make_and(menv, msat_make_equal(menv, x_x, nums[0]),
                            msat_make_equal(menv, x_id, s_id))
        rhs = msat_make_and(
            menv, rhs,
            msat_make_and(
                menv,
                msat_make_gt(menv, x, k),
                msat_make_not(menv, msat_make_equal(menv, s_id, pid))))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        # (l = wait & l' = cs) -> x' = x & id' = id & x > k & id = pid
        lhs = msat_make_and(menv, disc_t,
                            msat_make_and(menv, self.wait, self.x_cs))
        rhs = msat_make_and(menv, msat_make_equal(menv, x_x, x),
                            msat_make_equal(menv, x_id, s_id))
        rhs = msat_make_and(menv, rhs,
                            msat_make_and(
                                menv,
                                msat_make_gt(menv, x, k),
                                msat_make_equal(menv, s_id, pid)))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        # (l = cs) -> l' = idle & x' = x & id' = 0
        lhs = msat_make_and(menv, disc_t, self.cs)
        rhs = msat_make_and(menv, self.x_idle,
                            msat_make_and(menv,
                                          msat_make_equal(menv, x_x, x),
                                          msat_make_equal(menv, x_id,
                                                          nums[0])))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
