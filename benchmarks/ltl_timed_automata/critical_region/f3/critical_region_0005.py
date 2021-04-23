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

num_procs = 5
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

    N = msat_make_number(menv, str(num_procs))
    A = msat_make_number(menv, "25")
    B = msat_make_number(menv, "50")

    delta, x_delta = decl_consts(menv, delta_name, real_type)

    s_id, x_id = decl_consts(menv, "id", int_type)

    curr2next = {delta: x_delta, s_id: x_id}

    counter = Counter("c", menv, enc, N, delta, s_id, x_id)
    arbiters = [Arbiter("a{}".format(idx), menv, enc, idx + 1, delta,
                        s_id, x_id)
                for idx in range(num_procs)]
    prod_cells = [ProdCell("pc{}".format(idx), menv, enc, delta, A, B)
                  for idx in range(num_procs)]

    components = [counter, *arbiters, *prod_cells]
    for comp in components:
        for s, x_s in comp.symb2next.items():
            assert s not in curr2next.keys()
            curr2next[s] = x_s

    zero = msat_make_number(menv, "0")
    one = msat_make_number(menv, "1")

    init = msat_make_geq(menv, delta, zero)
    trans = msat_make_geq(menv, x_delta, zero)
    for comp in components:
        init = msat_make_and(menv, init, comp.init)
        trans = msat_make_and(menv, trans, comp.trans)

    # bound id
    bound_id = msat_make_equal(menv, s_id, zero)
    x_bound_id = msat_make_equal(menv, x_id, zero)
    for idx in range(1, num_procs):
        num = msat_make_number(menv, str(idx))
        bound_id = msat_make_or(menv, bound_id,
                                msat_make_equal(menv, s_id, num))
        x_bound_id = msat_make_or(menv, x_bound_id,
                                  msat_make_equal(menv, x_id, num))
    init = msat_make_and(menv, init, bound_id)
    trans = msat_make_and(menv, trans, x_bound_id)

    # all_stutter -> id' = id
    all_stutter = counter.evt_stutter
    for comp in components[1:]:
        all_stutter = msat_make_and(menv, all_stutter, comp.evt_stutter)
    trans = msat_make_and(menv, trans,
                          msat_make_impl(menv, all_stutter,
                                         msat_make_equal(menv, x_id, s_id)))

    d_eq_0 = msat_make_equal(menv, delta, zero)
    # sync arbiter and prodcell
    for arb, prod in zip(arbiters, prod_cells):
        trans = msat_make_and(menv, trans,
                              msat_make_impl(menv, d_eq_0,
                                             msat_make_iff(menv, arb.evt_enter,
                                                           prod.evt_enter)))
        trans = msat_make_and(menv, trans,
                              msat_make_impl(menv, d_eq_0,
                                             msat_make_iff(menv, arb.evt_exit,
                                                           prod.evt_exit)))

    # (G (pc0.l != error | pc1.l != error)) -> G F id = 1
    lhs = msat_make_or(menv,
                       msat_make_not(menv, prod_cells[0].error),
                       msat_make_not(menv, prod_cells[1].error))
    lhs = enc.make_G(lhs)
    rhs = enc.make_G(enc.make_F(msat_make_equal(menv, s_id, one)))
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


class Counter(Module):
    """Counter module"""
    def __init__(self, name: str, menv: msat_env, enc: LTLEncoder,
                 N, delta, s_id, x_id):
        super().__init__(name, menv, enc)

        bool_type = msat_get_bool_type(menv)

        move, x_move = self._symb("move", bool_type)
        l, x_l = self._symb("initial", bool_type)

        self.evt_move = move
        self.evt_stutter = msat_make_not(menv, move)

        self.symb2next = {move: x_move, l: x_l}

        zero = msat_make_number(menv, "0")
        one = msat_make_number(menv, "1")

        # l = initial
        self.init = l
        # evt_stutter | delta > 0 -> l' = l
        self.trans = msat_make_impl(
            menv,
            msat_make_or(menv, msat_make_gt(menv, delta, zero),
                         msat_make_not(menv, move)),
            msat_make_iff(menv, x_l, l))
        d_eq_0 = msat_make_equal(menv, delta, zero)
        # (!evt_stutter & l = initial) -> (id = 0 & id' = 1 & l' = initCount)
        lhs = msat_make_and(menv, move, l)
        lhs = msat_make_and(menv, lhs, d_eq_0)
        rhs = msat_make_and(menv,
                            msat_make_equal(menv, s_id, zero),
                            msat_make_equal(menv, x_id, one))
        rhs = msat_make_and(menv, rhs, msat_make_not(menv, x_l))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        # (!evt_stutter & l = initCount) -> (l' = initCount)
        lhs = msat_make_and(menv, d_eq_0, move)
        lhs = msat_make_and(menv, lhs, msat_make_not(menv, l))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs,
                                                  msat_make_not(menv, x_l)))
        # (l = initCount & l' = initCount & id >= N) -> (id' = 1)
        lhs = msat_make_and(menv, d_eq_0, msat_make_geq(menv, s_id, N))
        lhs = msat_make_and(menv, lhs,
                            msat_make_and(menv, msat_make_not(menv, l),
                                          msat_make_not(menv, x_l)))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs,
                                                  msat_make_equal(menv, x_id,
                                                                  one)))
        # (l = initCount & l' = initCount & id < N) -> (id' = id + 1)
        lhs = msat_make_and(menv, d_eq_0, msat_make_lt(menv, s_id, N))
        lhs = msat_make_and(menv, lhs,
                            msat_make_and(menv, msat_make_not(menv, l),
                                          msat_make_not(menv, x_l)))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs,
                                                  msat_make_equal(menv, x_id,
                                                                  one)))


class Arbiter(Module):
    """Arbiter module"""
    def __init__(self, name: str, menv: msat_env, enc: LTLEncoder,
                 i, delta, s_id, x_id):
        super().__init__(name, menv, enc)

        bool_type = msat_get_bool_type(menv)
        # int_type = msat_get_integer_type(menv)

        # evt, x_evt = self._symb("evt", int_type)
        evt_symbs, evts, x_evts = self._enum("evt", 3)

        loc, x_loc = self._symb("l", bool_type)
        s0 = loc
        x_s0 = x_loc
        s1 = msat_make_not(menv, loc)
        x_s1 = msat_make_not(menv, x_loc)

        self.symb2next = {loc: x_loc}
        for s, x_s in evt_symbs:
            assert s not in self.symb2next
            self.symb2next[s] = x_s

        zero = msat_make_number(menv, "0")
        i = msat_make_number(menv, str(i))

        self.evt_stutter = evts[0]
        self.evt_enter = evts[1]
        self.evt_exit = evts[2]

        x_evt_stutter = x_evts[0]
        x_evt_enter = x_evts[1]
        x_evt_exit = x_evts[2]

        evt_bounds = msat_make_or(menv, self.evt_stutter,
                                  msat_make_or(menv, self.evt_enter,
                                               self.evt_exit))
        self.init = msat_make_and(menv, evt_bounds, s1)
        self.trans = msat_make_or(menv, x_evt_stutter,
                                  msat_make_or(menv, x_evt_enter,
                                               x_evt_exit))
        # stutter | delta > 0 -> l' = l
        self.trans = msat_make_and(
            menv, self.trans,
            msat_make_impl(menv,
                           msat_make_or(menv, self.evt_stutter,
                                        msat_make_gt(menv, delta, zero)),
                           msat_make_iff(menv, x_loc, loc)))
        d_eq_0 = msat_make_equal(menv, delta, zero)
        not_stutter = msat_make_not(menv, self.evt_stutter)
        # (!evt_stutter & l = s1) -> (l' = s0 & evt_enter & id = i & id' = 0)
        lhs = msat_make_and(menv, d_eq_0, not_stutter)
        lhs = msat_make_and(menv, lhs, s1)
        rhs = msat_make_and(menv, x_s0, self.evt_enter)
        rhs = msat_make_and(menv, rhs, msat_make_equal(menv, s_id, i))
        rhs = msat_make_and(menv, rhs, msat_make_equal(menv, x_id, zero))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        # (!evt_stutter & l = s0) -> (l' = s1 & evt_exit & id' = i)
        lhs = msat_make_and(menv, d_eq_0, not_stutter)
        lhs = msat_make_and(menv, lhs, s0)
        rhs = msat_make_and(menv, x_s1, self.evt_exit)
        rhs = msat_make_and(menv, rhs, msat_make_equal(menv, x_id, i))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))


class ProdCell(Module):
    """ProdCell module"""
    def __init__(self, name: str, menv: msat_env, enc: LTLEncoder, delta,
                 A, B):
        super().__init__(name, menv, enc)

        # int_type = msat_get_integer_type(menv)
        real_type = msat_get_rational_type(menv)

        # evt, x_evt = self._symb("evt", int_type)
        evt_symbs, evts, x_evts = self._enum("evt", 4)
        # loc, x_loc = self._symb("l", int_type)
        loc_symbs, locs, x_locs = self._enum("l", 7)
        x, x_x = self._symb("x", real_type)

        self.symb2next = {x: x_x}
        for s, x_s in chain(evt_symbs, loc_symbs):
            assert s not in self.symb2next
            self.symb2next[s] = x_s

        nums = [msat_make_number(menv, str(n))
                for n in range(7)]

        self.evt_stutter = evts[0]
        self.evt_enter = evts[1]
        self.evt_exit = evts[2]
        self.evt_move = evts[3]

        x_evt_stutter = x_evts[0]
        x_evt_enter = x_evts[1]
        x_evt_exit = x_evts[2]
        x_evt_move = x_evts[3]

        self.not_ready = locs[0]
        self.testing = locs[1]
        self.requesting = locs[2]
        self.critical = locs[3]
        self.testing2 = locs[4]
        self.safe = locs[5]
        self.error = locs[6]

        x_not_ready = x_locs[0]
        x_testing = x_locs[1]
        x_requesting = x_locs[2]
        x_critical = x_locs[3]
        x_testing2 = x_locs[4]
        x_safe = x_locs[5]
        x_error = x_locs[6]

        same_loc = msat_make_iff(menv, loc_symbs[0][1], loc_symbs[0][0])
        for s, x_s in loc_symbs[1:]:
            same_loc = msat_make_and(menv, same_loc,
                                     msat_make_iff(menv, x_s, s))

        self.init = msat_make_and(menv, self.not_ready,
                                  msat_make_equal(menv, x, nums[0]))
        bound_evt = msat_make_or(menv,
                                 msat_make_or(menv, self.evt_stutter,
                                              self.evt_enter),
                                 msat_make_or(menv, self.evt_exit,
                                              self.evt_move))
        self.init = msat_make_and(menv, self.init, bound_evt)
        bound_loc = msat_make_or(menv,
                                 msat_make_or(menv, self.not_ready,
                                              self.testing),
                                 msat_make_or(menv, self.requesting,
                                              self.critical))
        bound_loc = msat_make_or(menv, bound_loc,
                                 msat_make_or(menv, self.testing2, self.safe))
        bound_loc = msat_make_or(menv, bound_loc, self.error)
        self.init = msat_make_and(menv, self.init, bound_loc)

        x_bound_evt = msat_make_or(menv,
                                   msat_make_or(menv, x_evt_stutter,
                                                x_evt_enter),
                                   msat_make_or(menv, x_evt_exit,
                                                x_evt_move))
        x_bound_loc = msat_make_or(
            menv,
            msat_make_or(menv, x_not_ready, x_testing),
            msat_make_or(menv, x_requesting, x_critical))
        x_bound_loc = msat_make_or(menv, x_bound_loc,
                                   msat_make_or(menv, x_testing2, x_safe))
        x_bound_loc = msat_make_or(menv, x_bound_loc, x_error)
        self.trans = msat_make_and(menv, x_bound_evt, x_bound_loc)

        # delta > 0 -> x' = x + delta & l' = l
        self.trans = msat_make_and(
            menv, self.trans,
            msat_make_impl(menv, msat_make_gt(menv, delta, nums[0]),
                           msat_make_and(
                               menv, same_loc,
                               msat_make_equal(menv, x_x,
                                               msat_make_plus(menv, x,
                                                              delta)))))
        # stutter -> x' = x + delta & l' = l
        self.trans = msat_make_and(
            menv, self.trans,
            msat_make_impl(menv, self.evt_stutter,
                           msat_make_and(
                               menv,
                               msat_make_equal(menv, x_x,
                                               msat_make_plus(menv, x, delta)),
                               same_loc)))
        d_eq_0 = msat_make_equal(menv, delta, nums[0])
        # (!evt_stutter & l = not_ready) -> (evt_move & x <= B & x' = 0 & l' = testing)
        lhs = msat_make_and(menv, d_eq_0,
                            msat_make_not(menv, self.evt_stutter))
        lhs = msat_make_and(menv, lhs, self.not_ready)
        rhs = msat_make_and(menv, self.evt_move, msat_make_leq(menv, x, B))
        rhs = msat_make_and(menv, rhs,
                            msat_make_and(menv,
                                          msat_make_equal(menv, x_x, nums[0]),
                                          x_testing))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        # (!evt_stutter & l = testing) -> ((l' = not_ready | l' = requesting) & evt_move)
        lhs = msat_make_and(menv, d_eq_0,
                            msat_make_not(menv, self.evt_stutter))
        lhs = msat_make_and(menv, lhs, self.testing)
        rhs = msat_make_and(menv, self.evt_move,
                            msat_make_or(menv, x_not_ready, x_requesting))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        # (l = testing & l' = not_ready) -> (x >= A_ & x' = 0)
        self.trans = msat_make_and(
            menv, self.trans,
            msat_make_impl(menv,
                           msat_make_and(menv, self.testing, x_not_ready),
                           msat_make_and(menv, msat_make_geq(menv, x, A),
                                         msat_make_equal(menv, x_x, nums[0]))))
        # (l = testing & l' = requesting) -> (x <= A_ - 1 & x' = x)
        self.trans = msat_make_and(
            menv, self.trans,
            msat_make_impl(menv,
                           msat_make_and(menv, self.testing, x_requesting),
                           msat_make_and(menv,
                                         msat_make_leq(menv, x,
                                                       msat_make_minus(menv, A,
                                                                       nums[1])),
                                         msat_make_equal(menv, x_x, x))))
        # (!evt_stutter & l = requesting) -> (l' = critical & evt_enter & x' = 0)
        lhs = msat_make_and(menv, d_eq_0,
                            msat_make_not(menv, self.evt_stutter))
        lhs = msat_make_and(menv, lhs, self.requesting)
        rhs = msat_make_and(menv, x_critical, self.evt_enter)
        rhs = msat_make_and(menv, rhs, msat_make_equal(menv, x_x, nums[0]))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        # (!evt_stutter & l = critical) -> (l' = error | l' = testing2)
        lhs = msat_make_and(menv, d_eq_0,
                            msat_make_not(menv, self.evt_stutter))
        lhs = msat_make_and(menv, lhs, self.critical)
        rhs = msat_make_or(menv, x_error, x_testing2)
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        # (l = critical & l' = error) -> (evt_move & x >= B & x' = x)
        lhs = msat_make_and(menv, self.critical, x_error)
        rhs = msat_make_and(menv, self.evt_move, msat_make_geq(menv, x, B))
        rhs = msat_make_and(menv, rhs, msat_make_equal(menv, x_x, x))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        # (l = critical & l' = testing2) -> (evt_exit & x <= A_ - 1 & x' = 0)
        lhs = msat_make_and(menv, self.critical, x_testing2)
        rhs = msat_make_and(menv, self.evt_exit, msat_make_leq(menv, x, A))
        rhs = msat_make_and(menv, rhs, msat_make_equal(menv, x_x, nums[0]))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        # (!evt_stutter & l = testing2) -> ((l' = error | l' = safe) & evt_move & x' = x)
        lhs = msat_make_and(menv, d_eq_0,
                            msat_make_not(menv, self.evt_stutter))
        lhs = msat_make_and(menv, lhs, self.testing2)
        rhs = msat_make_and(menv, self.evt_move, msat_make_equal(menv, x_x, x))
        rhs = msat_make_and(menv, rhs, msat_make_or(menv, x_error, x_safe))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        # (l = testing2 & l' = error) -> (x >= A_)
        lhs = msat_make_and(menv, self.testing2, x_error)
        rhs = msat_make_geq(menv, x, A)
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        # (l = testing2 & l' = safe) -> (x <= A_ - 1);
        lhs = msat_make_and(menv, self.testing2, x_safe)
        rhs = msat_make_leq(menv, x, msat_make_minus(menv, A, nums[1]))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        # (!evt_stutter & l = error) -> next(l) = error;
        lhs = msat_make_and(menv, d_eq_0,
                            msat_make_not(menv, self.evt_stutter))
        lhs = msat_make_and(menv, lhs, self.error)
        rhs = x_error
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        # (!evt_stutter & l = safe) -> l' = not_ready
        lhs = msat_make_and(menv, d_eq_0,
                            msat_make_not(menv, self.evt_stutter))
        lhs = msat_make_and(menv, lhs, self.safe)
        rhs = x_not_ready
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
