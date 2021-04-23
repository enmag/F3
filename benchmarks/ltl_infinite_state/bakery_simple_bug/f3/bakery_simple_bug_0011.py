from collections import Iterable
from math import log, ceil

from mathsat import msat_term, msat_env
from mathsat import msat_make_constant, msat_declare_function
from mathsat import msat_get_integer_type, msat_get_bool_type
from mathsat import msat_make_and, msat_make_not, msat_make_or, msat_make_iff
from mathsat import msat_make_leq, msat_make_equal, msat_make_true
from mathsat import msat_make_number, msat_make_plus, msat_make_times

from ltl.ltl import TermMap, LTLEncoder
from utils import name_next

num_procs = 11


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


def check_ltl(menv: msat_env, enc: LTLEncoder) -> (Iterable, msat_term,
                                                   msat_term, msat_term):
    assert menv
    assert isinstance(menv, msat_env)
    assert enc
    assert isinstance(enc, LTLEncoder)
    int_type = msat_get_integer_type(menv)

    numbers = [tuple(decl_consts(menv, "num{}".format(i), int_type))
               for i in range(num_procs)]
    x_numbers = [n[1] for n in numbers]
    numbers = [n[0] for n in numbers]

    min_num, x_min_num = decl_consts(menv, "min_num", int_type)
    max_num, x_max_num = decl_consts(menv, "max_num", int_type)

    run_symbs, runs, x_runs = make_enum(menv, "run", num_procs)

    curr2next = {min_num: x_min_num, max_num: x_max_num}
    for s, x_s in run_symbs:
        assert s not in curr2next
        curr2next[s] = x_s
    for n, x_n in zip(numbers, x_numbers):
        assert n not in curr2next
        curr2next[n] = x_n

    procs = [Proc("p{}".format(i), menv, enc,
                  i, runs[i], numbers, x_numbers,
                  min_num, x_min_num,
                  max_num, x_max_num)
             for i in range(num_procs)]

    for comp in procs:
        for s, x_s in comp.symb2next.items():
            assert s not in curr2next.keys()
            curr2next[s] = x_s

    zero = msat_make_number(menv, "0")

    all_nums_zero = msat_make_equal(menv, numbers[0], zero)
    for n in numbers[1:]:
        all_nums_zero = msat_make_and(menv, all_nums_zero,
                                      msat_make_equal(menv, n, zero))
    x_all_nums_zero = msat_make_equal(menv, x_numbers[0], zero)
    for x_n in x_numbers[1:]:
        x_all_nums_zero = msat_make_and(menv, x_all_nums_zero,
                                        msat_make_equal(menv, x_n, zero))
    init = all_nums_zero

    # bound run
    bound_run = runs[0]
    x_bound_run = x_runs[0]
    for r, x_r in zip(runs[1:], x_runs[1:]):
        bound_run = msat_make_or(menv, bound_run, r)
        x_bound_run = msat_make_or(menv, x_bound_run, x_r)
    init = msat_make_and(menv, init, bound_run)
    trans = x_bound_run

    # invars
    # max_num >= n for all n in numbers
    for n in numbers:
        init = msat_make_and(menv, init, msat_make_geq(menv, max_num, n))
    for x_n in x_numbers:
        trans = msat_make_and(menv, trans, msat_make_geq(menv, x_max_num, x_n))
    # \/_n in numbers: max_num = n
    curr = msat_make_equal(menv, max_num, numbers[0])
    for n in numbers[1:]:
        curr = msat_make_or(menv, curr, msat_make_equal(menv, max_num, n))
    init = msat_make_and(menv, init, curr)
    curr = msat_make_equal(menv, x_max_num, x_numbers[0])
    for x_n in x_numbers[1:]:
        curr = msat_make_or(menv, curr, msat_make_equal(menv, x_max_num, x_n))
    trans = msat_make_and(menv, trans, curr)
    # all numbers = 0 <-> min_num = 0
    init = msat_make_and(menv, init,
                         msat_make_iff(menv, all_nums_zero,
                                       msat_make_equal(menv, min_num, zero)))
    trans = msat_make_and(menv, trans,
                          msat_make_iff(menv, x_all_nums_zero,
                                        msat_make_equal(menv, x_min_num,
                                                        zero)))
    # n > 0 -> min_num <= n
    for n in numbers:
        curr = msat_make_impl(menv,
                              msat_make_gt(menv, n, zero),
                              msat_make_leq(menv, min_num, n))
        init = msat_make_and(menv, init, curr)
    for x_n in x_numbers:
        curr = msat_make_impl(menv,
                              msat_make_gt(menv, x_n, zero),
                              msat_make_leq(menv, x_min_num, x_n))
        trans = msat_make_and(menv, trans, curr)
    # min_num = n for some n
    curr = msat_make_equal(menv, min_num, numbers[0])
    for n in numbers[1:]:
        curr = msat_make_or(menv, curr, msat_make_equal(menv, min_num, n))
    init = msat_make_and(menv, init, curr)
    curr = msat_make_equal(menv, x_min_num, x_numbers[0])
    for x_n in x_numbers[1:]:
        curr = msat_make_or(menv, curr, msat_make_equal(menv, x_min_num, x_n))
    trans = msat_make_and(menv, trans, curr)

    for p in procs:
        init = msat_make_and(menv, init, p.init)
        trans = msat_make_and(menv, trans, p.trans)

    # (G ((F p0.pick_num) & (F !p0.pick_num))) -> (G F number[0] = 0)
    p = procs[0]
    lhs = msat_make_and(menv,
                        enc.make_F(p.pick_num),
                        enc.make_F(msat_make_not(menv, p.pick_num)))
    lhs = enc.make_G(lhs)
    rhs = enc.make_G(enc.make_F(msat_make_equal(menv, numbers[0], zero)))
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
        c_name = "{}_{}".format(self.name, v_name)
        return make_enum(self.menv, c_name, enum_size)


class Proc(Module):
    """Proc module"""
    def __init__(self, name: str, menv: msat_env, enc: LTLEncoder,
                 pid, run, numbers, x_numbers,
                 min_num, x_min_num, max_num, x_max_num):
        super().__init__(name, menv, enc)

        self.run = run
        loc_symbs, locs, x_locs = self._enum("l", 4)

        self.symb2next = {}
        for s, x_s in loc_symbs:
            assert s not in self.symb2next
            self.symb2next[s] = x_s

        self.pick_num = locs[0]
        self.wait_turn = locs[1]
        self.cs = locs[2]
        self.unlock = locs[3]
        self.x_pick_num = x_locs[0]
        self.x_wait_turn = x_locs[1]
        self.x_cs = x_locs[2]
        self.x_unlock = x_locs[3]

        same_loc = msat_make_iff(menv, loc_symbs[0][1], loc_symbs[0][0])
        for s, x_s in loc_symbs[1:]:
            same_loc = msat_make_and(menv, same_loc,
                                     msat_make_iff(menv, x_s, s))

        same_num_pid = msat_make_equal(menv, x_numbers[pid], numbers[pid])

        one = msat_make_number(menv, "1")

        # l = pick_num
        self.init = self.pick_num

        # bound l
        self.init = msat_make_and(
            menv, self.init,
            msat_make_or(menv,
                         msat_make_or(menv, self.pick_num, self.wait_turn),
                         msat_make_or(menv, self.cs, self.unlock)))
        self.trans = msat_make_or(
            menv,
            msat_make_or(menv, self.x_pick_num, self.x_wait_turn),
            msat_make_or(menv, self.x_cs, self.x_unlock))
        # ! run -> same_loc & number[id]' = number[id]
        lhs = msat_make_not(menv, run)
        rhs = msat_make_and(menv, same_loc, same_num_pid)
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        # (run & pick_num) -> (number[id]' = 1 + max_num & wait_turn')
        lhs = msat_make_and(menv, run, self.pick_num)
        rhs = msat_make_and(menv, self.x_wait_turn,
                            msat_make_equal(menv, x_numbers[pid],
                                            msat_make_plus(menv, max_num,
                                                           one)))
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        # (run & wait_turn) -> ((wait_turn' | cs') & same_num_pid)
        lhs = msat_make_and(menv, run, self.wait_turn)
        rhs = msat_make_and(menv,
                            msat_make_or(menv, self.x_wait_turn, self.x_cs),
                            same_num_pid)
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        # (run & wait_turn) -> (cs' <-> (number[id] <= min_num &
        # (number[i] = min_num -> id <= i) & ...
        lhs = msat_make_and(menv, run, self.wait_turn)
        rhs = msat_make_leq(menv, numbers[pid], min_num)
        for i in range(pid):
            curr = msat_make_not(menv, msat_make_equal(menv, numbers[i],
                                                       min_num))
            rhs = msat_make_and(menv, rhs, curr)
        rhs = msat_make_iff(menv, self.x_cs, rhs)
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        # (run & cs) -> (cs' | unlock') & same_num_pid
        lhs = msat_make_and(menv, run, self.cs)
        rhs = msat_make_and(menv,
                            msat_make_or(menv, self.x_cs, self.x_unlock),
                            same_num_pid)
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
        # (run & unlock) -> (pick_num' & number[id]' = number[id])
        lhs = msat_make_and(menv, run, self.unlock)
        rhs = msat_make_and(menv, self.x_pick_num, same_num_pid)
        self.trans = msat_make_and(menv, self.trans,
                                   msat_make_impl(menv, lhs, rhs))
