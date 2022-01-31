from typing import Iterable, Tuple
from mathsat import msat_term, msat_env
from mathsat import msat_make_constant, msat_declare_function
from mathsat import msat_get_integer_type, msat_get_bool_type
from mathsat import msat_make_and, msat_make_not, msat_make_or, msat_make_iff
from mathsat import msat_make_leq, msat_make_equal
from mathsat import msat_make_number, msat_make_plus
from ltl.ltl import TermMap, LTLEncoder
from expr_utils import name2next

num_procs = 10

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


def check_ltl(menv: msat_env, enc: LTLEncoder) -> Tuple[Iterable, msat_term,
                                                   msat_term, msat_term]:
    assert menv
    assert isinstance(menv, msat_env)
    assert enc
    assert isinstance(enc, LTLEncoder)
    int_type = msat_get_integer_type(menv)
    run = msat_declare_function(menv, "run", int_type)
    semaphore = msat_declare_function(menv, "semaphore", int_type)
    run = msat_make_constant(menv, run)
    semaphore = msat_make_constant(menv, semaphore)
    x_run = msat_declare_function(menv, name2next("run"), int_type)
    x_run = msat_make_constant(menv, x_run)
    x_semaphore = msat_declare_function(menv, name2next("semaphore"), int_type)
    x_semaphore = msat_make_constant(menv, x_semaphore)

    nums = [msat_make_number(menv, str(i)) for i in range(num_procs + 1)]
    proc_run = [msat_make_equal(menv, run, n) for n in nums[:-1]]
    G_F_proc_runs = enc.make_G(enc.make_F(proc_run[0]))
    for it in proc_run[1:]:
        G_F_proc_runs = msat_make_and(menv, G_F_proc_runs,
                                      enc.make_G(enc.make_F(it)))
    n_G_F_sem_eq_0 = enc.make_G(enc.make_F(msat_make_equal(menv, semaphore,
                                                           nums[0])))
    n_G_F_sem_eq_0 = msat_make_not(menv, n_G_F_sem_eq_0)
    # ((G F run = 0) & (G F run = 1) & ...) -> !(G F semaphore = 0);
    ltl = msat_make_impl(menv, G_F_proc_runs, n_G_F_sem_eq_0)

    curr2next = {run: x_run, semaphore: x_semaphore}

    # semaphore = 0
    init = msat_make_equal(menv, semaphore, nums[0])
    # semaphore = proc_num -> next(semaphore) = 0
    trans = msat_make_impl(menv, msat_make_equal(menv, semaphore, nums[-1]),
                           msat_make_equal(menv, x_semaphore, nums[0]))

    signal = msat_make_and(menv,
                           msat_make_equal(menv, semaphore, nums[-1]),
                           msat_make_equal(menv, x_semaphore, nums[0]))
    for i in range(num_procs):
        prefix = "sm{}".format(i)
        _curr2next, _init, _trans = semaphore_constrs(prefix, menv,
                                                      proc_run[i],
                                                      semaphore,
                                                      x_semaphore,
                                                      signal)
        for k, v in _curr2next.items():
            assert k not in curr2next
            curr2next[k] = v
        init = msat_make_and(menv, init, _init)
        trans = msat_make_and(menv, trans, _trans)

    return TermMap(curr2next), init, trans, ltl


def semaphore_constrs(name, menv, run, sem, x_sem, cont):
    int_type = msat_get_integer_type(menv)
    bool_type = msat_get_bool_type(menv)
    state = msat_declare_function(menv, "{}_state".format(name), bool_type)
    state = msat_make_constant(menv, state)
    x_state = msat_declare_function(menv, name2next("{}_state".format(name)),
                                    bool_type)
    x_state = msat_make_constant(menv, x_state)
    # state = work
    work = state
    x_work = x_state
    # state = wait
    wait = msat_make_not(menv, state)
    x_wait = msat_make_not(menv, x_state)

    loop_len = msat_declare_function(menv, "{}_loop_len".format(name),
                                     int_type)
    loop_len = msat_make_constant(menv, loop_len)
    x_loop_len = msat_declare_function(menv,
                                       name2next("{}_loop_len".format(name)),
                                       int_type)
    x_loop_len = msat_make_constant(menv, x_loop_len)

    l = msat_declare_function(menv, "{}_l".format(name), int_type)
    l = msat_make_constant(menv, l)
    x_l = msat_declare_function(menv, name2next("{}_l".format(name)), int_type)
    x_l = msat_make_constant(menv, x_l)

    curr2next = {state: x_state, loop_len: x_loop_len, l: x_l}
    m_one = msat_make_number(menv, "-1")
    zero = msat_make_number(menv, "0")
    one = msat_make_number(menv, "1")

    # state = work & loop_len > 0 & l = 0
    init = msat_make_and(menv, msat_make_gt(menv, loop_len, zero),
                         msat_make_equal(menv, l, zero))
    init = msat_make_and(menv, work, init)

    # (state = wait & state' = work) -> loop_len' > loop_len & l' = 0
    cond = msat_make_and(menv, wait, x_work)
    trans = msat_make_impl(menv, cond,
                           msat_make_and(menv,
                                         msat_make_gt(menv, x_loop_len,
                                                      loop_len),
                                         msat_make_equal(menv, l, zero)))
    # !(state = wait & state' = work) -> loop_len' = loop_len
    trans = msat_make_and(menv, trans,
                          msat_make_impl(menv, msat_make_not(menv, cond),
                                         msat_make_equal(menv, x_loop_len,
                                                         loop_len)))
    # state = work -> l' = l - 1
    trans = msat_make_and(
        menv, trans,
        msat_make_impl(menv, work,
                       msat_make_equal(menv, x_l,
                                       msat_make_plus(menv, l, m_one))))
    # state = work & l < loop_len -> state' = work
    trans = msat_make_and(menv, trans,
                          msat_make_impl(menv,
                                         msat_make_and(menv, work,
                                                       msat_make_lt(menv, l,
                                                                    loop_len)),
                                         x_work))
    # cont & state = wait -> state' = work
    trans = msat_make_and(menv, trans,
                          msat_make_impl(menv, msat_make_and(menv, cont, wait),
                                         x_work))
    # !run & !(cont & state = wait) -> state' = state
    same_state = msat_make_iff(menv, x_state, state)
    lhs = msat_make_not(menv, msat_make_and(menv, cont, wait))
    lhs = msat_make_and(menv, msat_make_not(menv, run), lhs)
    trans = msat_make_and(menv, trans,
                          msat_make_impl(menv, lhs,
                                         same_state))
    # run & next(state) = state -> next(sem) = sem
    trans = msat_make_and(menv, trans,
                          msat_make_impl(menv,
                                         msat_make_and(menv, run, same_state),
                                         msat_make_equal(menv, x_sem, sem)))
    # run & state = work & next(state) = wait -> next(sem) = sem + 1
    lhs = msat_make_and(menv, msat_make_and(menv, run, work), x_wait)
    trans = msat_make_and(menv, trans,
                          msat_make_impl(menv, lhs,
                                         msat_make_equal(menv, x_sem,
                                                         msat_make_plus(menv,
                                                                        sem,
                                                                        one))))
    return curr2next, init, trans
