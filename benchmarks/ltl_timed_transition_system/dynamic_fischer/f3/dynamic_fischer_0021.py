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

num_procs = 21

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

    bool_type = msat_get_bool_type(menv)
    real_type = msat_get_rational_type(menv)
    id_symbs, ids, x_ids = make_enum(menv, "id", num_procs + 1)
    turn_symbs, turns, x_turns = make_enum(menv, "turn", num_procs)
    proposed = [tuple(decl_consts(menv, "proposed{}".format(i), real_type))
                for i in range(num_procs)]
    x_proposed = [p[1] for p in proposed]
    proposed = [p[0] for p in proposed]
    max_prop, x_max_prop = decl_consts(menv, "max_prop", real_type)
    delta, x_delta = decl_consts(menv, delta_name, real_type)
    inc_max_prop, x_inc_max_prop = decl_consts(menv, "inc_max_prop", bool_type)

    same_id = msat_make_iff(menv, id_symbs[0][1], id_symbs[0][0])
    for s, x_s in id_symbs[1:]:
        same_id = msat_make_and(menv, same_id,
                                msat_make_iff(menv, x_s, s))
    same_turn = msat_make_iff(menv, turn_symbs[0][1], turn_symbs[0][0])
    for s, x_s in turn_symbs[1:]:
        same_turn = msat_make_and(menv, same_turn,
                                  msat_make_iff(menv, x_s, s))
    procs = [Proc("p{}".format(i), menv, enc, turns[i],
                  ids[i], x_ids[i], ids[-1], x_ids[-1],
                  proposed[i], x_proposed[i],
                  same_id, max_prop, delta, x_delta)
             for i in range(num_procs)]

    curr2next = {max_prop: x_max_prop, delta: x_delta,
                  inc_max_prop: x_inc_max_prop}
    for s, x_s in chain(id_symbs, turn_symbs):
        assert s not in curr2next
        curr2next[s] = x_s
    for s, x_s in zip(proposed, x_proposed):
        assert s not in curr2next
        curr2next[s] = x_s
    for comp in procs:
        for s, x_s in comp.symb2next.items():
            curr2next[s] = x_s

    # bound id
    bound_id = ids[0]
    for c_id in ids[1:]:
        bound_id = msat_make_or(menv, bound_id, c_id)
    init = bound_id
    bound_id = x_ids[0]
    for x_id in x_ids[1:]:
        bound_id = msat_make_or(menv, bound_id, x_id)
    trans = bound_id

    # bound turn
    bound_turn = turns[0]
    for c_t in turns[1:]:
        bound_turn = msat_make_or(menv, bound_turn, c_t)
    init = msat_make_and(menv, init, bound_turn)
    bound_turn = x_turns[0]
    for x_t in x_turns[1:]:
        bound_turn = msat_make_or(menv, bound_turn, x_t)
    trans = msat_make_and(menv, trans, bound_turn)

    # id = 0 & inc_max_prop
    init = msat_make_and(menv, init, msat_make_and(menv, ids[0], inc_max_prop))

    zero = msat_make_number(menv, "0")

    # delta > 0 -> id' = id & turn' = turn &
    # max_prop' = max_prop
    lhs = msat_make_gt(menv, delta, zero)
    rhs = msat_make_and(menv, msat_make_and(menv, same_id, same_turn),
                        x_inc_max_prop)
    trans = msat_make_and(menv, trans,
                          msat_make_impl(menv, lhs, rhs))
    # invar: delta >= 0
    init = msat_make_and(menv, init, msat_make_geq(menv, delta, zero))
    trans = msat_make_and(menv, trans, msat_make_geq(menv, x_delta, zero))
    # invar: max_prop >= proposed[0] & ...
    for prop, x_prop in zip(proposed, x_proposed):
        init = msat_make_and(menv, init,
                             msat_make_geq(menv, max_prop, prop))
        trans = msat_make_and(menv, trans,
                              msat_make_geq(menv, x_max_prop, x_prop))
    # invar: max_prop = proposed[0] | ...
    init_eqs = msat_make_equal(menv, max_prop, proposed[0])
    trans_eqs = msat_make_equal(menv, x_max_prop, x_proposed[0])
    for p, x_p in zip(proposed[1:], x_proposed[1:]):
        init_eqs = msat_make_or(menv, init_eqs,
                                msat_make_equal(menv, max_prop, p))
        trans_eqs = msat_make_or(menv, trans_eqs,
                                 msat_make_equal(menv, x_max_prop, x_p))
    init = msat_make_and(menv, init, init_eqs)
    trans = msat_make_and(menv, trans, trans_eqs)

    # max_prop' >= max_prop <-> inc_max_prop'
    lhs = msat_make_geq(menv, x_max_prop, max_prop)
    rhs = x_inc_max_prop
    trans = msat_make_and(menv, trans,
                          msat_make_iff(menv, lhs, rhs))

    for p in procs:
        init = msat_make_and(menv, init, p.init)
        trans = msat_make_and(menv, trans, p.trans)

    # F G inc_max_prop
    ltl = enc.make_F(enc.make_G(inc_max_prop))
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
        c_name = "{}_{}".format(self.name, v_name)
        return make_enum(self.menv, c_name, enum_size)


class Proc(Module):
    """P module"""
    def __init__(self, name: str, menv: msat_env, enc: LTLEncoder,
                 run, mid, x_mid, id0, x_id0,
                 prop, x_prop, same_id, max_prop,
                 delta, x_delta):
        super().__init__(name, menv, enc)

        real_type = msat_get_rational_type(menv)
        loc_symbs, locs, x_locs = self._enum("l", 4)
        x, x_x = self._symb("x", real_type)
        saved, x_saved = self._symb("saved_max", real_type)

        idle = locs[0]
        wait = locs[1]
        req = locs[2]
        cs = locs[3]
        x_idle = x_locs[0]
        x_wait = x_locs[1]
        x_req = x_locs[2]
        x_cs = x_locs[3]

        self.symb2next = {x: x_x, saved: x_saved}
        for s, x_s in loc_symbs:
            assert s not in self.symb2next
            self.symb2next[s] = x_s

        same_loc = msat_make_iff(menv, loc_symbs[0][1], loc_symbs[0][0])
        for s, x_s in loc_symbs[1:]:
            same_loc = msat_make_and(menv, same_loc,
                                     msat_make_iff(menv, x_s, s))
        # bound loc
        self.init = msat_make_or(menv,
                                 msat_make_or(menv, idle, wait),
                                 msat_make_or(menv, req, cs))
        self.trans = msat_make_or(menv,
                                  msat_make_or(menv, x_idle, x_wait),
                                  msat_make_or(menv, x_req, x_cs))
        zero = msat_make_number(menv, "0")

        # idle & x = 0 & saved_max = max_prop
        self.init = msat_make_and(
            menv,
            msat_make_and(menv, self.init, idle),
            msat_make_and(menv,
                          msat_make_equal(menv, x, zero),
                          msat_make_equal(menv, saved, max_prop)))
        # invar: prop > 0
        self.init = msat_make_and(menv, self.init,
                                  msat_make_gt(menv, prop, zero))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_gt(menv, x_prop, zero))
        # invar: (location = req) -> x <= prop
        self.init = msat_make_and(
            menv, self.init,
            msat_make_impl(menv, req, msat_make_leq(menv, x, prop)))
        self.trans = msat_make_and(
            menv, self.trans,
            msat_make_impl(menv, x_req, msat_make_leq(menv, x_x, x_prop)))

        # (delta > 0 | !run) -> loc' = loc & x' = x + delta &
        # saved_max' = saved_max & prop' = prop
        lhs = msat_make_or(menv,
                           msat_make_gt(menv, delta, zero),
                           msat_make_not(menv, run))
        rhs = msat_make_and(
            menv,
            msat_make_and(menv, same_loc,
                          msat_make_equal(menv, x_x,
                                          msat_make_plus(menv, x, delta))),
            msat_make_and(menv,
                          msat_make_equal(menv, x_saved, saved),
                          msat_make_equal(menv, x_prop, prop)))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))

        disc_t = msat_make_and(menv, run, msat_make_equal(menv, delta, zero))
        # loc = idle ->  (loc' = req & x' = 0 & id' = id &
        # prop' = prop & saved_max' = max_prop)
        lhs = msat_make_and(menv, disc_t, idle)
        rhs = msat_make_and(menv,
                            msat_make_and(menv, x_req,
                                          msat_make_equal(menv, x_x, zero)),
                            msat_make_and(menv, same_id,
                                          msat_make_equal(menv, x_prop, prop)))
        rhs = msat_make_and(menv, rhs,
                            msat_make_equal(menv, x_saved, max_prop))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        # loc = req  ->  (loc' = wait & x' = 0 & id' = pid & prop' = prop &
        # saved_max' = max_prop)
        lhs = msat_make_and(menv, disc_t, req)
        rhs = msat_make_and(menv,
                            msat_make_and(menv, x_wait,
                                          msat_make_equal(menv, x_x, zero)),
                            msat_make_and(menv, x_mid,
                                          msat_make_equal(menv, x_prop, prop)))
        rhs = msat_make_and(menv, rhs,
                            msat_make_equal(menv, x_saved, max_prop))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        # loc = wait -> (id' = id & prop' = prop & saved' = max_prop &
        # (loc' = idle & x' = 0) | (loc' = cs & x' = x))
        disj = msat_make_or(menv,
                            msat_make_and(menv, x_idle,
                                          msat_make_equal(menv, x_x, zero)),
                            msat_make_and(menv, x_cs,
                                          msat_make_equal(menv, x_x, x)))
        lhs = msat_make_and(menv, disc_t, wait)
        rhs = msat_make_and(
            menv,
            msat_make_and(menv, same_id,
                          msat_make_equal(menv, x_prop, prop)),
            msat_make_and(menv,
                          msat_make_equal(menv, x_saved, max_prop),
                          disj))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        # loc = cs -> (loc' = idle & x' = x & id' = 0 & prop' < prop &
        # saved_max' = max_prop)
        lhs = msat_make_and(menv, disc_t, cs)
        rhs = msat_make_and(menv,
                            msat_make_and(menv, x_idle,
                                          msat_make_equal(menv, x_x, x)),
                            msat_make_and(menv, x_id0,
                                          msat_make_lt(menv, x_prop, prop)))
        rhs = msat_make_and(menv, rhs,
                            msat_make_equal(menv, x_saved, max_prop))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
