from typing import FrozenSet, Iterator
from math import gcd

from pysmt.environment import Environment as PysmtEnv
from pysmt.fnode import FNode
import pysmt.typing as types

from mathsat import msat_term, msat_env
from mathsat import msat_make_constant, msat_declare_function
from mathsat import msat_get_rational_type, msat_get_integer_type, \
    msat_get_bool_type
from mathsat import msat_make_and, msat_make_not, msat_make_or, msat_make_iff
from mathsat import msat_make_leq, msat_make_equal, msat_make_true
from mathsat import msat_make_number, msat_make_plus, msat_make_times, \
    msat_make_divide

from ltl.ltl import TermMap, LTLEncoder
from expr_utils import name2next, symb2next
from hint import Hint, Location

DELTA_NAME = "delta"
MIN_ACC = -1
MAX_ACC = 2
NUM_FOLLOWERS = 1
PERIODS = [1, 2]


def math_lcm(a, b):
    return abs(a*b) // gcd(a, b)


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
    delta = msat_declare_function(menv, DELTA_NAME, real_type)
    delta = msat_make_constant(menv, delta)
    return frozenset([delta])


def check_ltl(menv: msat_env, enc: LTLEncoder):
    assert menv
    assert isinstance(menv, msat_env)
    assert enc
    assert isinstance(enc, LTLEncoder)
    real_type = msat_get_rational_type(menv)

    zero = msat_make_number(menv, "0")
    min_acc = msat_make_number(menv, str(MIN_ACC))
    max_acc = msat_make_number(menv, str(MAX_ACC))

    delta, x_delta = decl_consts(menv, DELTA_NAME, real_type)
    leader_period = msat_make_number(menv, str(PERIODS[0]))
    leader = Leader(menv, "leader", leader_period, min_acc, max_acc,
                    delta, x_delta)
    followers = [None] * NUM_FOLLOWERS
    followers[0] = Follower(menv, "follower{}".format(0), leader,
                            msat_make_number(menv, str(PERIODS[1])),
                            min_acc, max_acc, delta, x_delta)
    for i in range(1, NUM_FOLLOWERS):
        followers[i] = Follower(menv, "follower{}".format(i), followers[i - 1],
                                msat_make_number(menv, str(PERIODS[i+1])),
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


def hints(env: PysmtEnv):
    assert isinstance(env, PysmtEnv)

    mgr = env.formula_manager
    min_acc = mgr.Real(MIN_ACC)
    max_acc = mgr.Real(MAX_ACC)
    delta = mgr.Symbol(f"{DELTA_NAME}", types.REAL)
    symbs = [delta]
    symbs.extend(Leader.pysmt_symbs("leader", env))
    for i in range(NUM_FOLLOWERS):
        symbs.extend(Follower.pysmt_symbs(f"follower{i}", env))
    symbs = frozenset(symbs)

    hints = [delta_c_hint(env, delta, symbs)]
    # hints.extend(Leader.get_hints("leader", env, symbs, mgr.Real(PERIODS[0]),
    #                               min_acc, max_acc, delta))
    # other_a = mgr.Symbol(Leader.A_NAME.format("leader"), types.REAL)
    # other_v = mgr.Symbol(Leader.V_NAME.format("leader"), types.REAL)

    # for i in range(NUM_FOLLOWERS):
    #     hints.extend(Follower.get_hints(i, f"follower{i}", env, symbs,
    #                                     mgr.Real(PERIODS[i+1]), min_acc,
    #                                     max_acc, delta, other_a, other_v))
    #     other_a = mgr.Symbol(Follower.A_NAME.format(f"follower{i}"), types.REAL)
    #     other_v = mgr.Symbol(Follower.V_NAME.format(f"follower{i}"), types.REAL)
    return frozenset(hints)


class Leader:
    """Transition system describing the Leader"""
    A_NAME = "{}_a"
    V_NAME = "{}_v"
    C_NAME = "{}_c"
    TRAVEL_NAME = "{}_travel"

    @staticmethod
    def pysmt_symbs(name: str, env: PysmtEnv) -> FrozenSet[FNode]:
        assert isinstance(name, str)
        assert isinstance(env, PysmtEnv)
        mgr = env.formula_manager
        return frozenset([mgr.Symbol(Leader.A_NAME.format(name), types.REAL),
                          mgr.Symbol(Leader.V_NAME.format(name), types.REAL),
                          mgr.Symbol(Leader.C_NAME.format(name), types.REAL),
                          mgr.Symbol(Leader.TRAVEL_NAME.format(name), types.REAL)])

    @staticmethod
    def get_hints(name: str, env: PysmtEnv, symbs: FrozenSet[FNode],
                  period: FNode, min_acc: FNode, max_acc: FNode,
                  delta: FNode) -> Iterator[Hint]:
        assert isinstance(name, str)
        assert isinstance(env, PysmtEnv)
        assert isinstance(symbs, frozenset)
        assert all(isinstance(s, FNode) for s in symbs)
        assert isinstance(period, FNode)
        assert isinstance(min_acc, FNode)
        assert isinstance(max_acc, FNode)
        assert isinstance(delta, FNode)

        mgr = env.formula_manager
        a = mgr.Symbol(Leader.A_NAME.format(name), types.REAL)
        v = mgr.Symbol(Leader.V_NAME.format(name), types.REAL)

        r_0 = mgr.Real(0)

        x_a = symb2next(env, a)
        invar = mgr.And(mgr.LE(r_0, a), mgr.LE(a, max_acc))
        loc0 = Location(env, invar, stutterT=mgr.Equals(x_a, a))
        loc0.set_progress(0, mgr.And(mgr.LE(r_0, x_a),
                                          mgr.LE(x_a, max_acc)))
        loc0.set_progress(1, mgr.Equals(x_a, r_0))
        loc1 = Location(env, mgr.Equals(a, r_0), stutterT=mgr.Equals(x_a, a))
        loc1.set_progress(0, mgr.And(mgr.LE(r_0, x_a),
                                          mgr.LE(x_a, max_acc)))
        loc0.set_progress(1, mgr.Equals(x_a, r_0))
        hint_a = Hint("h_a", env, frozenset([a]), symbs)
        hint_a.set_locs([loc0, loc1])
        yield hint_a

        x_v = symb2next(env, v)
        assume = mgr.And(mgr.GE(delta, r_0), mgr.GE(a, r_0))
        loc = Location(env, mgr.LE(r_0, v), assume)
        loc.set_progress(0,
                         mgr.Equals(x_v, mgr.Plus(v, mgr.Times(delta, a))))
        hint_v = Hint("h_v", env, frozenset([v]), symbs)
        hint_v.set_locs([loc])
        yield hint_v

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
        self.a, self.x_a = decl_consts(menv, Leader.A_NAME.format(name),
                                       real_type)
        self.v, self.x_v = decl_consts(menv, Leader.V_NAME.format(name),
                                       real_type)
        self.c, self.x_c = decl_consts(menv, Leader.C_NAME.format(name),
                                       real_type)
        self.travel, self.x_travel = decl_consts(menv,
                                                 Leader.TRAVEL_NAME.format(name),
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
    A_NAME = "{}_a"
    V_NAME = "{}_v"
    C_NAME = "{}_c"
    DIST_NAME = "{}_dist"

    @staticmethod
    def pysmt_symbs(name: str, env: PysmtEnv) -> FrozenSet[FNode]:
        assert isinstance(name, str)
        assert isinstance(env, PysmtEnv)
        mgr = env.formula_manager
        return frozenset([mgr.Symbol(Follower.A_NAME.format(name), types.REAL),
                          mgr.Symbol(Follower.V_NAME.format(name), types.REAL),
                          mgr.Symbol(Follower.C_NAME.format(name), types.REAL),
                          mgr.Symbol(Follower.DIST_NAME.format(name), types.REAL)])

    @staticmethod
    def get_hints(i: int, name: str, env: PysmtEnv, symbs: FrozenSet[FNode],
                  period: FNode, min_acc: FNode, max_acc: FNode, delta: FNode,
                  other_a: FNode, other_v: FNode) -> Iterator[Hint]:
        assert isinstance(i, int)
        assert isinstance(name, str)
        assert isinstance(env, PysmtEnv)
        assert isinstance(symbs, frozenset)
        assert all(isinstance(s, FNode) for s in symbs)
        assert isinstance(period, FNode)
        assert isinstance(min_acc, FNode)
        assert isinstance(max_acc, FNode)
        assert isinstance(delta, FNode)
        assert isinstance(other_a, FNode)
        assert isinstance(other_v, FNode)

        mgr = env.formula_manager
        a = mgr.Symbol(Follower.A_NAME.format(name), types.REAL)
        v = mgr.Symbol(Follower.V_NAME.format(name), types.REAL)
        dist = mgr.Symbol(Follower.DIST_NAME.format(name), types.REAL)

        m_1 = mgr.Real(-1)
        r_0 = mgr.Real(0)
        r_2 = mgr.Real(2)

        x_a = symb2next(env, a)
        loc = Location(env, mgr.Equals(a, r_0))
        loc.set_progress(0, mgr.Equals(x_a, r_0))
        hint_a = Hint(f"h{i}_a", env, frozenset([a]), symbs)
        hint_a.set_locs([loc])
        yield hint_a

        x_v = symb2next(env, v)
        x_dist = symb2next(env, dist)
        invar = mgr.And(mgr.GT(v, r_0),
                        mgr.GT(dist,
                               mgr.Minus(mgr.Times(period, v),
                                         mgr.Div(mgr.Times(v, v),
                                                 mgr.Times(r_2, min_acc)))))
        assume = mgr.And(mgr.GE(delta, r_0), mgr.Equals(a, r_0),
                         mgr.GE(other_a, r_0), mgr.GE(other_v, v))
        loc = Location(env, invar, assume)
        x_dist_val = mgr.Plus(
            dist, mgr.Times(other_v, delta),
            mgr.Div(mgr.Times(other_a, delta, delta), r_2),
            mgr.Times(m_1, v, delta))
        loc.set_progress(0, mgr.And(mgr.Equals(x_v, v),
                                         mgr.Equals(x_dist, x_dist_val)))
        hint_dist = Hint(f"h{i}_v_dist", env, frozenset([v, dist]), symbs)
        hint_dist.set_locs([loc])
        yield hint_dist

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
        self.a, self.x_a = decl_consts(menv, Follower.A_NAME.format(name),
                                       real_type)
        self.v, self.x_v = decl_consts(menv, Follower.V_NAME.format(name),
                                       real_type)
        self.c, self.x_c = decl_consts(menv, Follower.C_NAME.format(name),
                                       real_type)
        self.dist, self.x_dist = decl_consts(menv, Follower.DIST_NAME.format(name),
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


def delta_c_hint(env: PysmtEnv, delta: FNode, symbs: FrozenSet[FNode]) -> Hint:
    assert isinstance(env, PysmtEnv)
    assert isinstance(delta, FNode)
    assert isinstance(symbs, frozenset)
    assert all(isinstance(s, FNode) for s in symbs)

    def clock_value(mgr, curr_time: float, period: int, keep_period: bool):
        val = curr_time % period
        return mgr.Real(period if keep_period and val == 0 else val)

    def clock_x_value(mgr, curr_time: float, period: int, c: FNode):
        reset = (curr_time % period) == 0
        return mgr.Real(0) if reset else mgr.Plus(c, delta)

    lcm = PERIODS[0]
    for p in PERIODS[1:]:
        lcm = math_lcm(lcm, p)

    times = [s for s in range(1, lcm+1)
             if any((s % p) == 0 for s in PERIODS)]
    mgr = env.formula_manager
    r_0 = mgr.Real(0)
    x_delta = symb2next(env, delta)
    comps_c = [mgr.Symbol(Leader.C_NAME.format("leader"),
                          types.REAL)]
    comps_c.extend(mgr.Symbol(Leader.C_NAME.format(f"follower{i}"),
                              types.REAL)
                   for i in range(NUM_FOLLOWERS))
    assert len(comps_c) == len(PERIODS)
    owned_symbs = [delta]
    owned_symbs.extend(comps_c)

    locs = []
    for idx in range(len(times)):
        x_idx = (idx + 1) % len(times)
        c_time = times[idx] if x_idx > 0 else 0
        x_time = times[x_idx]
        assert x_time > c_time
        t_step = x_time - c_time
        x_delta_val = mgr.Real(t_step)
        # regions
        invar = [mgr.Equals(comp_c, clock_value(mgr, c_time, comp_period, True))
                 for comp_c, comp_period in zip(comps_c, PERIODS)]
        invar.append(mgr.Equals(delta, r_0))
        c_loc = Location(env, mgr.And(invar))
        locs.append(c_loc)

        invar = [mgr.Equals(comp_c, clock_value(mgr, c_time, comp_period, False))
                 for comp_c, comp_period in zip(comps_c, PERIODS)]
        invar.append(mgr.Equals(delta, x_delta_val))
        x_loc = Location(env, mgr.And(invar))
        locs.append(x_loc)

        # transitions
        assert len(locs) == 2 * idx + 2
        disc_trans = [mgr.Equals(x_delta, x_delta_val)]
        disc_trans.extend(mgr.Equals(symb2next(env, c),
                                     clock_x_value(mgr, c_time,
                                                   period, c))
                          for c, period in zip(comps_c, PERIODS))
        c_loc.set_progress(2 * idx + 1, mgr.And(disc_trans))
        xx_loc_idx = (2 * idx + 2) % (2 * len(times))
        timed_trans = [mgr.Equals(x_delta, r_0)]
        timed_trans.extend(mgr.Equals(symb2next(env, c), mgr.Plus(c, delta))
                           for c in comps_c)
        x_loc.set_progress(xx_loc_idx, mgr.And(timed_trans))

    h_delta = Hint("h_deltac", env, frozenset(owned_symbs), symbs)
    h_delta.set_locs(locs)

    return h_delta
