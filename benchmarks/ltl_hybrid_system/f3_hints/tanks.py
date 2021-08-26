from pysmt.environment import Environment as PysmtEnv
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
from utils import name_next, symb_to_next
from hint import Hint, Location


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

    delta, x_delta = decl_consts(menv, delta_name, real_type)
    vol_in, x_vol_in = decl_consts(menv, "tot_vol_in", real_type)
    vol_out, x_vol_out = decl_consts(menv, "tot_vol_out", real_type)

    _0 = msat_make_number(menv, "0")
    half = msat_make_number(menv, "0.5")
    _1 = msat_make_number(menv, "1")
    _10 = msat_make_number(menv, "10")
    _100 = msat_make_number(menv, "100")

    # components
    max_flows = [_10, _1, _1]
    max_speeds = [_1, _1, _1]
    assert len(max_speeds) == len(max_flows)
    pipes = [
        Pipe(menv, f"pipe{i}", delta, x_delta, max_flows[i],
             max_speeds[i]) for i in range(len(max_speeds))
    ]

    max_vols = [_100, _10]
    in_pipes = [[pipes[0]], [pipes[1]]]
    out_pipes = [[pipes[1]], [pipes[2]]]
    assert len(max_vols) == len(in_pipes)
    assert len(max_vols) == len(out_pipes)

    in_flows = []
    for i in range(len(max_vols)):
        acc = _0
        for f in in_pipes[i]:
            acc = msat_make_plus(menv, acc, f.flow)
        in_flows.append(acc)
    out_flows = []
    for i in range(len(max_vols)):
        acc = _0
        for f in out_pipes[i]:
            acc = msat_make_plus(menv, acc, f.flow)
        out_flows.append(acc)
    flows = []
    for i in range(len(max_vols)):
        flows.append(msat_make_minus(menv, in_flows[i], out_flows[i]))
    in_d_flows = []
    for i in range(len(max_vols)):
        acc = _0
        for f in in_pipes[i]:
            acc = msat_make_plus(menv, acc, f.d_flow)
        in_d_flows.append(acc)
    out_d_flows = []
    for i in range(len(max_vols)):
        acc = _0
        for f in out_pipes[i]:
            acc = msat_make_plus(menv, acc, f.d_flow)
        out_d_flows.append(acc)
    d_flows = []
    for i in range(len(max_vols)):
        d_flows.append(msat_make_minus(menv, in_d_flows[i], out_d_flows[i]))

    tanks = [
        Tank(menv, f"tank{i}", delta, x_delta, max_vols[i], flows[i],
             d_flows[i]) for i in range(len(max_vols))
    ]
    components = pipes + tanks

    curr2next = {delta: x_delta, vol_in: x_vol_in, vol_out: x_vol_out}
    for comp in components:
        for s, x_s in comp.curr2next.items():
            assert s not in curr2next
            curr2next[s] = x_s

    # initial location.
    init = msat_make_and(menv,
                         msat_make_geq(menv, delta, _0),
                         msat_make_and(menv,
                                       msat_make_equal(menv, vol_in, _0),
                                       msat_make_equal(menv, vol_out, _0)))
    for comp in components:
        init = msat_make_and(menv, init,
                             msat_make_and(menv, comp.init, comp.invar))
    # transition relation.
    add_vol = _0
    for f in in_pipes[0]:
        el = msat_make_plus(
            menv,
            msat_make_times(menv, f.flow, delta),
            msat_make_times(menv,
                            msat_make_times(menv, half, f.d_flow),
                            msat_make_times(menv, delta, delta)))
        add_vol = msat_make_plus(menv, add_vol, el)
    sub_vol = _0
    for f in out_pipes[-1]:
        el = msat_make_plus(
            menv,
            msat_make_times(menv, f.flow, delta),
            msat_make_times(menv,
                            msat_make_times(menv, half, f.d_flow),
                            msat_make_times(menv, delta, delta)))
        sub_vol = msat_make_plus(menv, sub_vol, el)

    trans = msat_make_and(
        menv, msat_make_geq(menv, x_delta, _0),
        msat_make_and(menv,
                      msat_make_equal(menv, x_vol_in,
                                      msat_make_plus(menv, vol_in, add_vol)),
                      msat_make_equal(menv, x_vol_out,
                                      msat_make_plus(menv, vol_out, sub_vol))))
    for comp in components:
        trans = msat_make_and(menv, trans,
                              msat_make_and(menv, comp.x_invar, comp.trans))

    fairness = msat_make_gt(menv, pipes[-1].flow, _0)
    ltl = enc.make_F(enc.make_G(msat_make_not(menv, fairness)))
    return curr2next, init, trans, ltl


class Tank:
    """Transition system describing a Tank"""

    _VOL_NAME = "_vol"

    @staticmethod
    def pysmt_symbs(env: PysmtEnv, name: str):
        return [env.formula_manager.Symbol(f"{name}{Tank._VOL_NAME}",
                                           types.REAL)]

    @staticmethod
    def hints(env: PysmtEnv, name: str, delta, flow, d_flow, max_flow,
              symbs):
        mgr = env.formula_manager
        vol = mgr.Symbol(f"{name}{Tank._VOL_NAME}", types.REAL)
        x_vol = symb_to_next(mgr, vol)
        res = []
        # if name == "tank0":
        #     m_1 = mgr.Real(-1)
        #     r_0 = mgr.Real(0)
        #     r_5 = mgr.Real(5)
        #     r_6 = mgr.Real(6)
        #     r_7 = mgr.Real(7)
        #     r_35 = mgr.Real(35)
        #     r_40 = mgr.Real(40)
        #     r_45_2 = mgr.Div(mgr.Real(45), mgr.Real(2))
        #     loc0 = Location(env, mgr.Equals(vol, r_5),
        #                     mgr.And(mgr.Equals(flow, mgr.Times(m_1, max_flow)),
        #                             mgr.Equals(delta, r_7)))
        #     loc0.set_progress(1, mgr.Equals(x_vol, r_45_2))
        #     loc1 = Location(env, mgr.Equals(vol, r_45_2),
        #                     mgr.And(mgr.Equals(flow, r_6),
        #                             mgr.Equals(d_flow, m_1),
        #                             mgr.Equals(delta, r_7)))
        #     loc1.set_progress(2, mgr.Equals(x_vol, r_40))
        #     loc2 = Location(env, mgr.Equals(vol, r_40),
        #                     mgr.And(mgr.Equals(flow, mgr.Times(m_1, max_flow)),
        #                             mgr.Equals(d_flow, r_0),
        #                             mgr.Equals(delta, r_35)))
        #     loc2.set_progress(0, mgr.Equals(x_vol, r_5))
        #     hint = Hint("h_vol0", env, frozenset([vol]), symbs)
        #     hint.set_locs([loc0, loc1, loc2])
        #     res.append(hint)
        return res

    def __init__(self, menv: msat_env, name: str, delta,
                 x_delta, max_vol, flow, d_flow):
        real_type = msat_get_rational_type(menv)
        self.menv = menv
        self.name = name
        self.max_vol = max_vol
        self.flow = flow
        self.d_flow = d_flow
        self.delta = delta
        self.x_delta = x_delta
        self.vol, self.x_vol = decl_consts(menv, f"{name}{Tank._VOL_NAME}",
                                           real_type)

    @property
    def curr2next(self) -> dict:
        """ Return dictionary of current-next symbols"""
        return {self.vol: self.x_vol}

    @property
    def init(self):
        """Return formula representing the initial states"""
        return msat_make_equal(self.menv, self.vol,
                               msat_make_number(self.menv, "0"))

    @property
    def invar(self):
        """Return formula representing the invariant"""
        menv = self.menv
        _0 = msat_make_number(menv, "0")
        return msat_make_and(menv,
                             msat_make_leq(menv, _0, self.vol),
                             msat_make_leq(menv, self.vol, self.max_vol))

    @property
    def x_invar(self):
        """Return formula representing the invariant"""
        menv = self.menv
        _0 = msat_make_number(menv, "0")
        return msat_make_and(menv,
                             msat_make_leq(menv, _0, self.x_vol),
                             msat_make_leq(menv, self.x_vol, self.max_vol))

    @property
    def trans(self):
        """Returns formula representing the transition relation"""
        menv = self.menv
        _2 = msat_make_number(menv, "2")
        f_d = msat_make_times(menv, self.flow, self.delta)
        df_dd = msat_make_times(menv, self.d_flow,
                                msat_make_times(menv, self.delta, self.delta))
        expr = msat_make_divide(menv, df_dd, _2)
        expr = msat_make_plus(menv, f_d, expr)
        expr = msat_make_plus(menv, self.vol, expr)
        return msat_make_equal(menv, self.x_vol, expr)


class Pipe:
    """Transition system describing a Pipe."""

    _MODE_NAME = "_mode"
    _FLOW_NAME = "_flow"
    _DFLOW_NAME = "_dflow"
    _CLOSE = 0
    _OPENING = 1
    _OPEN = 2
    _CLOSING = 3

    @staticmethod
    def pysmt_symbs(env: PysmtEnv, name: str):
        mgr = env.formula_manager
        return [mgr.Symbol(f"{name}{Pipe._MODE_NAME}", types.INT),
                mgr.Symbol(f"{name}{Pipe._FLOW_NAME}", types.REAL),
                mgr.Symbol(f"{name}{Pipe._DFLOW_NAME}", types.REAL)]

    @staticmethod
    def hints(env: PysmtEnv, name: str, delta, symbs):
        mgr = env.formula_manager
        mode = mgr.Symbol(f"{name}{Pipe._MODE_NAME}", types.INT)
        flow = mgr.Symbol(f"{name}{Pipe._FLOW_NAME}", types.REAL)
        dflow = mgr.Symbol(f"{name}{Pipe._DFLOW_NAME}", types.REAL)
        res = []
        if name == "pipe0":
            r_0 = mgr.Real(0)
            r_7 = mgr.Real(7)
            r_35 = mgr.Real(35)
            x_mode = symb_to_next(mgr, mode)
            x_flow = symb_to_next(mgr, flow)
            opening = mgr.Equals(mode, mgr.Int(Pipe._OPENING))
            x_opening = mgr.Equals(x_mode, mgr.Int(Pipe._OPENING))
            closing = mgr.Equals(mode, mgr.Int(Pipe._CLOSING))
            x_closing = mgr.Equals(x_mode, mgr.Int(Pipe._CLOSING))
            close = mgr.Equals(mode, mgr.Int(Pipe._CLOSE))
            x_close = mgr.Equals(x_mode, mgr.Int(Pipe._CLOSE))
            loc0 = Location(env,
                            mgr.And(opening, mgr.Equals(flow, r_0)),
                            mgr.Equals(delta, r_7))
            loc0.set_progress(1, mgr.And(x_closing,
                                              mgr.Equals(x_flow, r_7)))
            loc1 = Location(env, mgr.And(closing, mgr.Equals(flow, r_7)),
                            mgr.Equals(delta, r_7))
            loc1.set_progress(2, mgr.And(x_close, mgr.Equals(x_flow, r_0)))
            loc2 = Location(env, mgr.And(close, mgr.Equals(flow, r_0)),
                            mgr.Equals(delta, r_35))
            loc2.set_progress(0, mgr.And(x_opening, mgr.Equals(x_flow, r_0)))
            hint = Hint("h_modeflow0", env, frozenset([mode, flow]), symbs)
            hint.set_locs([loc0, loc1, loc2])
            res.append(hint)

        return res


    def __init__(self, menv: msat_env, name: str, delta,
                 x_delta, max_flow, speed):
        self.menv = menv
        self.name = name
        self.delta = delta
        self.x_delta = x_delta
        self.max_flow = max_flow
        self.speed = speed

        int_type = msat_get_integer_type(menv)
        real_type = msat_get_rational_type(menv)

        self.mode, self.x_mode = decl_consts(menv, f"{name}{Pipe._MODE_NAME}",
                                             int_type)
        self.flow, self.x_flow = decl_consts(menv, f"{name}{Pipe._FLOW_NAME}",
                                             real_type)
        self.d_flow, self.x_d_flow = decl_consts(menv, f"{name}{Pipe._DFLOW_NAME}",
                                                 real_type)

    @property
    def curr2next(self) -> dict:
        """Return list of current-next symbols"""
        return {self.mode: self.x_mode, self.flow: self.x_flow,
                self.d_flow: self.x_d_flow}

    @property
    def close(self):
        menv = self.menv
        return msat_make_equal(menv, self.mode,
                               msat_make_number(menv, str(Pipe._CLOSE)))

    @property
    def x_close(self):
        menv = self.menv
        return msat_make_equal(menv, self.x_mode,
                               msat_make_number(menv, str(Pipe._CLOSE)))

    @property
    def opening(self):
        menv = self.menv
        return msat_make_equal(menv, self.mode,
                               msat_make_number(menv, str(Pipe._OPENING)))

    @property
    def x_opening(self):
        menv = self.menv
        return msat_make_equal(menv, self.x_mode,
                               msat_make_number(menv, str(Pipe._OPENING)))

    @property
    def open(self):
        menv = self.menv
        return msat_make_equal(menv, self.mode,
                               msat_make_number(menv, str(Pipe._OPEN)))

    @property
    def x_open(self):
        menv = self.menv
        return msat_make_equal(menv, self.x_mode,
                               msat_make_number(menv, str(Pipe._OPEN)))

    @property
    def closing(self):
        menv = self.menv
        return msat_make_equal(menv, self.mode,
                               msat_make_number(menv, str(Pipe._CLOSING)))

    @property
    def x_closing(self):
        menv = self.menv
        return msat_make_equal(menv, self.x_mode,
                               msat_make_number(menv, str(Pipe._CLOSING)))

    @property
    def init(self):
        """Return formula representing the initial states"""
        return self.close

    @property
    def invar(self):
        """Return formula representing the invariant"""
        menv = self.menv
        res = msat_make_or(menv,
                           msat_make_or(menv, self.open, self.opening),
                           msat_make_or(menv, self.close, self.closing))

        m_1 = msat_make_number(menv, "-1")
        _0 = msat_make_number(menv, "0")
        _1 = msat_make_number(menv, "1")
        res = msat_make_and(
            menv, res,
            msat_make_impl(menv,
                           msat_make_or(menv, self.close, self.open),
                           msat_make_equal(menv, self.d_flow, _0)))

        res = msat_make_and(
            menv, res,
            msat_make_and(menv,
                          msat_make_impl(menv, self.opening,
                                         msat_make_equal(menv, self.d_flow, _1)),
                          msat_make_impl(menv, self.closing,
                                         msat_make_equal(menv, self.d_flow, m_1))))

        res = msat_make_and(menv, res,
                            msat_make_impl(menv, self.close,
                                           msat_make_equal(menv, self.flow, _0)))

        res = msat_make_and(menv, res,
                            msat_make_impl(menv, self.open,
                                           msat_make_equal(menv, self.flow,
                                                           self.max_flow)))

        return msat_make_and(
            menv, res,
            msat_make_and(menv,
                          msat_make_leq(menv, _0, self.flow),
                          msat_make_leq(menv, self.flow, self.max_flow)))

    @property
    def x_invar(self):
        """Return formula representing the invariant"""
        menv = self.menv
        res = msat_make_or(menv,
                           msat_make_or(menv, self.x_open, self.x_opening),
                           msat_make_or(menv, self.x_close, self.x_closing))

        m_1 = msat_make_number(menv, "-1")
        _0 = msat_make_number(menv, "0")
        _1 = msat_make_number(menv, "1")
        res = msat_make_and(
            menv, res,
            msat_make_impl(menv,
                           msat_make_or(menv, self.x_close, self.x_open),
                           msat_make_equal(menv, self.x_d_flow, _0)))

        res = msat_make_and(
            menv, res,
            msat_make_and(menv,
                          msat_make_impl(menv, self.x_opening,
                                         msat_make_equal(menv, self.x_d_flow, _1)),
                          msat_make_impl(menv, self.x_closing,
                                         msat_make_equal(menv, self.x_d_flow, m_1))))

        res = msat_make_and(menv, res,
                            msat_make_impl(menv, self.x_close,
                                           msat_make_equal(menv, self.x_flow, _0)))

        res = msat_make_and(menv, res,
                            msat_make_impl(menv, self.x_open,
                                           msat_make_equal(menv, self.x_flow,
                                                           self.max_flow)))

        return msat_make_and(
            menv, res,
            msat_make_and(menv,
                          msat_make_leq(menv, _0, self.x_flow),
                          msat_make_leq(menv, self.x_flow, self.max_flow)))

    @property
    def trans(self):
        """Returns formula representing the transition relation"""
        menv = self.menv
        _0 = msat_make_number(menv, "0")
        flow_plus = msat_make_plus(menv, self.flow,
                                   msat_make_times(menv, self.speed, self.delta))
        flow_minus = msat_make_minus(menv, self.flow,
                                     msat_make_times(menv, self.speed, self.delta))
        lhs = self.opening
        rhs = msat_make_equal(menv, self.x_flow, flow_plus)
        res = msat_make_impl(menv, lhs, rhs)

        lhs = self.closing
        rhs = msat_make_equal(menv, self.x_flow, flow_minus)
        res = msat_make_and(menv, res, msat_make_impl(menv, lhs, rhs))

        lhs = msat_make_and(menv, self.opening,
                            msat_make_equal(menv, self.max_flow, flow_plus))
        rhs = msat_make_or(menv, self.x_open, self.x_closing)
        res = msat_make_and(menv, res, msat_make_impl(menv, lhs, rhs))

        lhs = msat_make_and(menv, self.opening,
                            msat_make_lt(menv, self.max_flow, flow_plus))
        rhs = msat_make_or(menv, self.x_opening, self.x_closing)
        res = msat_make_and(menv, res, msat_make_impl(menv, lhs, rhs))

        lhs = msat_make_and(menv, self.opening,
                            msat_make_equal(menv, _0, flow_minus))
        rhs = msat_make_or(menv, self.x_close, self.x_opening)
        res = msat_make_and(menv, res, msat_make_impl(menv, lhs, rhs))

        lhs = msat_make_and(menv, self.opening,
                            msat_make_lt(menv, _0, flow_minus))
        rhs = msat_make_or(menv, self.x_closing, self.x_opening)
        res = msat_make_and(menv, res, msat_make_impl(menv, lhs, rhs))
        return res


def hints(env: PysmtEnv):
    assert isinstance(env, PysmtEnv)

    mgr = env.formula_manager
    delta = mgr.Symbol(delta_name, types.REAL)
    vol_in = mgr.Symbol("tot_vol_in", types.REAL)
    vol_out = mgr.Symbol("tot_vol_out", types.REAL)

    r_1 = mgr.Real(1)
    r_10 = mgr.Real(10)
    r_100 = mgr.Real(100)
    max_speeds = [r_1, r_1, r_1]
    max_vols = [r_100, r_10]
    symbs = set([delta, vol_in, vol_out])
    for i in range(len(max_speeds)):
        symbs.update(Pipe.pysmt_symbs(env, f"pipe{i}"))
    for i in range(len(max_vols)):
        symbs.update(Tank.pysmt_symbs(env, f"tank{i}"))
    symbs = frozenset(symbs)

    r_7 = mgr.Real(7)
    r_35 = mgr.Real(35)

    x_delta = symb_to_next(mgr, delta)
    loc0 = Location(env, mgr.Equals(delta, r_7))
    loc0.set_progress(1, mgr.Equals(x_delta, r_7))
    loc1 = Location(env, mgr.Equals(delta, r_7))
    loc1.set_progress(2, mgr.Equals(x_delta, r_35))
    loc2 = Location(env, mgr.Equals(delta, r_35))
    loc2.set_progress(0, mgr.Equals(x_delta, r_7))
    hint_delta = Hint("h_delta", env, frozenset([delta]), symbs)
    hint_delta.set_locs([loc0, loc1, loc2])

    res = [hint_delta]
    for i in range(len(max_speeds)):
        res.extend(Pipe.hints(env, f"pipe{i}", delta, symbs))
    for i in range(len(max_vols)):
        res.extend(Tank.hints(env, f"tank{i}", delta, symbs))

    return frozenset(res)
