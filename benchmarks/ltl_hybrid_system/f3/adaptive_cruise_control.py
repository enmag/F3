from mathsat import msat_term, msat_env
from mathsat import msat_make_constant, msat_declare_function
from mathsat import msat_get_rational_type, msat_get_integer_type, \
    msat_get_bool_type
from mathsat import msat_make_and, msat_make_not, msat_make_or, msat_make_iff
from mathsat import msat_make_leq, msat_make_equal, msat_make_true
from mathsat import msat_make_number, msat_make_plus, msat_make_times, \
    msat_make_divide

from ltl.ltl import TermMap, LTLEncoder
from utils import name_next

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


def check_ltl(menv: msat_env, enc: LTLEncoder):
    assert menv
    assert isinstance(menv, msat_env)
    assert enc
    assert isinstance(enc, LTLEncoder)
    real_type = msat_get_rational_type(menv)

    zero = msat_make_number(menv, "0")
    num_followers = 1
    periods = [1, 1]
    min_acc = msat_make_number(menv, "-1")
    max_acc = msat_make_number(menv, "2")

    delta, x_delta = decl_consts(menv, delta_name, real_type)
    leader_period = msat_make_number(menv, str(periods[0]))
    leader = Leader(menv, "leader", leader_period, min_acc, max_acc,
                    delta, x_delta)
    followers = [None] * num_followers
    followers[0] = Follower(menv, "follower{}".format(0), leader,
                            msat_make_number(menv, str(periods[1])),
                            min_acc, max_acc, delta, x_delta)
    for i in range(1, num_followers):
        followers[i] = Follower(menv, "follower{}".format(i), followers[i - 1],
                                msat_make_number(menv, str(periods[i+1])),
                                min_acc, max_acc, delta, x_delta)
    components = [leader] + followers

    curr2next = {delta: x_delta}
    for comp in components:
        for s, x_s in comp.curr2next.items():
            assert s not in curr2next
            curr2next[s] = x_s

    # init location
    init = msat_make_geq(menv, delta, zero)
    for comp in components:
        init = msat_make_and(menv, init,
                             msat_make_and(menv, comp.init, comp.invar))
    # transition relation
    trans = msat_make_geq(menv, x_delta, zero)
    for comp in components:
        trans = msat_make_and(menv, trans,
                              msat_make_and(menv, comp.x_invar, comp.trans))

    # ltl
    ltl = msat_make_not(menv, enc.make_G(enc.make_F(msat_make_and(
        menv,
        msat_make_gt(menv, delta, zero),
        msat_make_gt(menv, leader.v, zero)))))
    return TermMap(curr2next), init, trans, ltl


class Leader:
    """Transition system describing the Leader"""
    def __init__(self, menv: msat_env, name: str, period,
                 min_acc, max_acc, delta, x_delta):
        real_type = msat_get_rational_type(menv)
        self.menv = menv
        self.name = name
        self.period = period
        self.min_acc = min_acc
        self.max_acc = max_acc
        self.delta = delta
        self.x_delta = x_delta
        self.a, self.x_a = decl_consts(menv, f"{name}_a", real_type)
        self.v, self.x_v = decl_consts(menv, f"{name}_v", real_type)
        self.c, self.x_c = decl_consts(menv, f"{name}_c", real_type)
        self.travel, self.x_travel = decl_consts(menv, f"{name}_travel",
                                                 real_type)

    @property
    def curr2next(self) -> dict:
        """ Return dictionary of symbols: current to next"""
        return {self.a: self.x_a, self.v: self.x_v, self.c: self.x_c,
                self.travel: self.x_travel}

    @property
    def init(self):
        """Return formula representing the initial states"""
        menv = self.menv
        zero = msat_make_number(menv, "0")
        return msat_make_and(menv,
                             msat_make_and(menv,
                                           msat_make_equal(menv, self.a, zero),
                                           msat_make_equal(menv, self.travel, zero)),
                             msat_make_and(menv,
                                           msat_make_equal(menv, self.v, zero),
                                           msat_make_equal(menv, self.c, zero)))

    @property
    def invar(self):
        """Return formula representing the invariant"""
        menv = self.menv
        zero = msat_make_number(menv, "0")
        v_p_a_delta = msat_make_plus(menv, self.v,
                                     msat_make_times(menv, self.a, self.delta))
        zero_le_c = msat_make_leq(menv, zero, self.c)
        c_le_period = msat_make_leq(menv, self.c, self.period)
        v_ge_zero = msat_make_geq(menv, self.v, zero)
        v_p_a_delta_ge_zero = msat_make_geq(menv, v_p_a_delta, zero)
        min_acc_le_a = msat_make_leq(menv, self.min_acc, self.a)
        a_le_max_acc = msat_make_leq(menv, self.a, self.max_acc)
        res = msat_make_and(menv,
                            msat_make_and(menv, zero_le_c, c_le_period),
                            msat_make_and(menv, v_ge_zero, v_p_a_delta_ge_zero))
        return msat_make_and(menv, res,
                             msat_make_and(menv, min_acc_le_a, a_le_max_acc))

    @property
    def x_invar(self):
        """Return formula representing the invariant"""
        menv = self.menv
        zero = msat_make_number(menv, "0")
        v_p_a_delta = msat_make_plus(menv, self.x_v,
                                     msat_make_times(menv, self.x_a, self.x_delta))
        zero_le_c = msat_make_leq(menv, zero, self.x_c)
        c_le_period = msat_make_leq(menv, self.x_c, self.period)
        v_ge_zero = msat_make_geq(menv, self.x_v, zero)
        v_p_a_delta_ge_zero = msat_make_geq(menv, v_p_a_delta, zero)
        min_acc_le_a = msat_make_leq(menv, self.min_acc, self.x_a)
        a_le_max_acc = msat_make_leq(menv, self.x_a, self.max_acc)
        res = msat_make_and(menv,
                            msat_make_and(menv, zero_le_c, c_le_period),
                            msat_make_and(menv, v_ge_zero, v_p_a_delta_ge_zero))
        return msat_make_and(menv, res,
                             msat_make_and(menv, min_acc_le_a, a_le_max_acc))

    @property
    def trans(self):
        """Returns formula representing the transition relation"""
        menv = self.menv
        zero = msat_make_number(menv, "0")
        c_eq_period = msat_make_equal(menv, self.c, self.period)
        xc_eq_zero = msat_make_equal(menv, self.x_c, zero)
        delta_eq_zero = msat_make_equal(menv, self.delta, zero)
        c_lt_period = msat_make_lt(menv, self.c, self.period)
        xc_eq_c_p_delta = msat_make_equal(menv, self.x_c,
                                          msat_make_plus(menv, self.c,
                                                         self.delta))
        xa_eq_a = msat_make_equal(menv, self.x_a, self.a)
        xa_eq_zero = msat_make_equal(menv, self.x_a, zero)
        xv_eq_v_p_a_delta = msat_make_equal(
            menv, self.x_v,
            msat_make_plus(menv, self.v,
                           msat_make_times(menv, self.a, self.delta)))
        xv_eq_zero = msat_make_equal(menv, self.x_v, zero)
        res = msat_make_and(
            menv,
            msat_make_impl(menv, c_eq_period,
                           msat_make_and(menv, xc_eq_zero, delta_eq_zero)),
            msat_make_impl(menv, c_lt_period,
                           xc_eq_c_p_delta))
        lhs = msat_make_and(menv, delta_eq_zero,
                            msat_make_and(menv, c_eq_period, xc_eq_zero))
        lhs = msat_make_not(menv, lhs)
        res = msat_make_and(
            menv, res,
            msat_make_impl(menv, lhs,
                           msat_make_or(menv, xa_eq_a, xa_eq_zero)))
        next_travel = msat_make_plus(menv, self.travel,
                                     msat_make_times(menv, self.v, self.delta))
        next_travel = msat_make_plus(
            menv, next_travel,
            msat_make_times(menv,
                            msat_make_times(menv, msat_make_number(menv, "0.5"),
                                            self.a),
                            msat_make_times(menv, self.delta, self.delta)))
        res = msat_make_and(
            menv, res,
            msat_make_and(menv,
                          msat_make_or(menv, xv_eq_v_p_a_delta,
                                       msat_make_and(menv, xv_eq_zero, xa_eq_zero)),
                          msat_make_equal(menv, self.x_travel, next_travel)))
        return res


class Follower:
    """Transition system describing a Follower vehicle."""
    def __init__(self, menv: msat_env, name: str, vehicle, period,
                 min_acc, max_acc, delta, x_delta):
        self.menv = menv
        self.name = name
        self.vehicle = vehicle
        self.period = period
        self.min_acc = min_acc
        self.max_acc = max_acc
        self.delta = delta
        self.x_delta = x_delta
        real_type = msat_get_rational_type(menv)
        self.a, self.x_a = decl_consts(menv, "{}_a".format(name), real_type)
        self.v, self.x_v = decl_consts(menv, "{}_v".format(name), real_type)
        self.c, self.x_c = decl_consts(menv, "{}_c".format(name), real_type)
        self.dist, self.x_dist = decl_consts(menv, "{}_dist".format(name),
                                             real_type)

    @property
    def curr2next(self) -> dict:
        """ Return dictionary of symbols: current to next"""
        return {self.a: self.x_a, self.v: self.x_v, self.c: self.x_c,
                self.dist: self.x_dist}

    @property
    def init(self):
        """Return formula representing the initial states"""
        menv = self.menv
        zero = msat_make_number(menv, "0")
        one = msat_make_number(menv, "1")
        return msat_make_and(
            menv,
            msat_make_and(menv,
                          msat_make_equal(menv, self.a, zero),
                          msat_make_equal(menv, self.v, zero)),
            msat_make_and(menv,
                          msat_make_equal(menv, self.c, zero),
                          msat_make_equal(menv, self.dist, one)))

    @property
    def invar(self):
        """Return formula representing the invariant"""
        menv = self.menv
        zero = msat_make_number(menv, "0")
        zero_le_c = msat_make_leq(menv, zero, self.c)
        c_le_period = msat_make_leq(menv, self.c, self.period)
        v_ge_zero = msat_make_geq(menv, self.v, zero)
        v_p_a_delta_ge_zero = msat_make_geq(
            menv,
            msat_make_plus(menv, self.v,
                           msat_make_times(menv, self.a, self.delta)),
            zero)
        min_acc_le_a = msat_make_leq(menv, self.min_acc, self.a)
        a_le_max_acc = msat_make_leq(menv, self.a, self.max_acc)
        return msat_make_and(
            menv,
            msat_make_and(menv,
                          msat_make_and(menv, zero_le_c, c_le_period),
                          msat_make_and(menv, v_ge_zero, v_p_a_delta_ge_zero)),
            msat_make_and(menv, min_acc_le_a, a_le_max_acc))

    @property
    def x_invar(self):
        """Return formula representing the invariant"""
        menv = self.menv
        zero = msat_make_number(menv, "0")
        zero_le_c = msat_make_leq(menv, zero, self.x_c)
        c_le_period = msat_make_leq(menv, self.x_c, self.period)
        v_ge_zero = msat_make_geq(menv, self.x_v, zero)
        v_p_a_delta_ge_zero = msat_make_geq(
            menv,
            msat_make_plus(menv, self.x_v,
                           msat_make_times(menv, self.x_a, self.x_delta)),
            zero)
        min_acc_le_a = msat_make_leq(menv, self.min_acc, self.x_a)
        a_le_max_acc = msat_make_leq(menv, self.x_a, self.max_acc)
        return msat_make_and(
            menv,
            msat_make_and(menv,
                          msat_make_and(menv, zero_le_c, c_le_period),
                          msat_make_and(menv, v_ge_zero, v_p_a_delta_ge_zero)),
            msat_make_and(menv, min_acc_le_a, a_le_max_acc))

    @property
    def trans(self):
        """Returns formula representing the transition relation"""
        menv = self.menv
        m_1 = msat_make_number(menv, "-1")
        r_0 = msat_make_number(menv, "0")
        half = msat_make_number(menv, "0.5")
        r_2 = msat_make_number(menv, "2")
        delta_eq_0 = msat_make_equal(menv, self.delta, r_0)
        c_eq_period = msat_make_equal(menv, self.c, self.period)
        c_lt_period = msat_make_lt(menv, self.c, self.period)
        xc_eq_0 = msat_make_equal(menv, self.x_c, r_0)
        xc_eq_c_p_delta = msat_make_equal(menv, self.x_c,
                                          msat_make_plus(menv, self.c,
                                                         self.delta))
        x_v_eq_v_p_ad = msat_make_equal(
            menv, self.x_v,
            msat_make_plus(menv, self.v,
                           msat_make_times(menv, self.a, self.delta)))
        end_speed = msat_make_plus(menv, self.v,
                                   msat_make_times(menv, self.x_a, self.period))
        controller = msat_make_and(menv,
                                   msat_make_and(menv, delta_eq_0, c_eq_period),
                                   xc_eq_0)
        # distance of vehicle ahead after `delta` from self current position.
        add = msat_make_times(menv, self.a,
                              msat_make_times(menv, self.delta, self.delta))
        half_add = msat_make_times(menv, half, add)
        vd = msat_make_times(menv, self.v, self.delta)
        vehicle_dist = msat_make_plus(menv, self.dist,
                                      msat_make_plus(menv, vd, half_add))
        # movement of self in next `delta`.
        curr_dist = msat_make_plus(menv, vd, half_add)
        # new distance after delta.
        next_dist = msat_make_minus(menv, vehicle_dist, curr_dist)
        vp = msat_make_times(menv, self.v, self.period)
        m_vp = msat_make_times(menv, m_1, vp)
        xa_pp = msat_make_times(menv, self.x_a,
                                msat_make_times(menv, self.period, self.period))
        half_xa_pp = msat_make_times(menv, half, xa_pp)
        two_min_acc = msat_make_times(menv, r_2, self.min_acc)
        acc_bound = msat_make_divide(menv,
                                     msat_make_times(menv, end_speed, end_speed),
                                     two_min_acc)
        acc_bound = msat_make_plus(menv,
                                   msat_make_plus(menv, self.dist, m_vp),
                                   msat_make_plus(menv, half_xa_pp, acc_bound))
        acc_bound_gt_0 = msat_make_gt(menv, acc_bound, r_0)
        res = msat_make_impl(menv, c_eq_period,
                             msat_make_and(menv, xc_eq_0, delta_eq_0))
        res = msat_make_and(menv, res,
                            msat_make_impl(menv, c_lt_period, xc_eq_c_p_delta))
        res = msat_make_and(menv, res,
                            msat_make_impl(menv, controller, acc_bound_gt_0))
        res = msat_make_and(menv, res,
                            msat_make_impl(menv, msat_make_not(menv, controller),
                                           msat_make_equal(menv, self.x_a,
                                                           self.a)))
        res = msat_make_and(menv, res,
                            msat_make_and(menv, x_v_eq_v_p_ad,
                                          msat_make_equal(menv, self.x_dist,
                                                          next_dist)))
        return res
