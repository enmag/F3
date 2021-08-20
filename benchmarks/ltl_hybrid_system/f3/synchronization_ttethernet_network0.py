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

    _0 = msat_make_number(menv, "0")
    _1 = msat_make_number(menv, "1")
    _2 = msat_make_number(menv, "2")
    _3 = msat_make_number(menv, "3")
    _4 = msat_make_number(menv, "4")
    _10 = msat_make_number(menv, "10")
    delay = _2
    drifts = [_3, _2, _4, _1, _10]

    delta, x_delta = decl_consts(menv, delta_name, real_type)
    cms = [
        ComprMaster(menv, "cm{}".format(i), delay, delta, x_delta)
        for i in range(2)
    ]
    sms = [
        SyncMaster(menv, "sm{}".format(i), drifts[i], delta, x_delta)
        for i in range(5)
    ]
    components = cms + sms

    curr2next = {delta: x_delta}
    for comp in components:
        for s, x_s in comp.curr2next.items():
            assert s not in curr2next
            curr2next[s] = x_s

    sync_constr = sync_on_broadcast_messages(menv, cms, sms)
    for cm in cms:
        curr = sync_comprmaster_syncmaster(menv, cm, sms[0])
        for sm in sms[1:]:
            curr = msat_make_and(menv, curr,
                                 sync_comprmaster_syncmaster(menv, cm, sm))
        sync_constr = msat_make_and(menv, sync_constr, curr)

    init = msat_make_geq(menv, delta, _0)
    trans = msat_make_and(menv, msat_make_geq(menv, x_delta, _0),
                          sync_constr)
    for comp in components:
        init = msat_make_and(menv, init,
                             msat_make_and(menv, comp.init, comp.invar))
        trans = msat_make_and(menv, trans,
                              msat_make_and(menv, comp.trans, comp.x_invar))

    # LTL F G !(all sm in sms: sm = sm_val)
    avg_cm = cms[0].cm
    for cm in cms[1:]:
        avg_cm = msat_make_plus(menv, avg_cm, cm.cm)
    avg_cm = msat_make_divide(menv, avg_cm,
                              msat_make_number(menv, str(len(cms))))
    fairness = msat_make_equal(menv, sms[0].sm, avg_cm)
    for sm in sms[1:]:
        fairness = msat_make_and(menv, fairness,
                                 msat_make_equal(menv, sm.sm, avg_cm))
    ltl = enc.make_F(enc.make_G(msat_make_not(menv, fairness)))
    return TermMap(curr2next), init, trans, ltl


class ComprMaster:
    """Transition system describing a ComprMaster"""
    def __init__(self, menv: msat_env, name: str, delay,
                 delta, x_delta):
        self.menv = menv
        self.name = name
        self.delay = delay
        real_type = msat_get_rational_type(menv)
        int_type = msat_get_integer_type(menv)
        self.delta = delta
        self.x_delta = x_delta
        self.mode, self.x_mode = decl_consts(menv, "{}_mode".format(name),
                                             int_type)
        self.cm, self.x_cm = decl_consts(menv, "{}_cm".format(name), real_type)
        self.x, self.x_x = decl_consts(menv, "{}_x".format(name), real_type)

    @property
    def waiting(self):
        """Return formula that holds iff state is waiting"""
        menv = self.menv
        return msat_make_equal(menv, self.mode,
                               msat_make_number(menv, "0"))

    @property
    def x_waiting(self):
        """Return formula that holds iff next state is waiting"""
        menv = self.menv
        return msat_make_equal(menv, self.x_mode,
                               msat_make_number(menv, "0"))

    @property
    def receive(self):
        """Return formula that holds iff state is receive"""
        menv = self.menv
        return msat_make_equal(menv, self.mode,
                               msat_make_number(menv, "1"))

    @property
    def x_receive(self):
        """Return formula that holds iff next state is receive"""
        menv = self.menv
        return msat_make_equal(menv, self.x_mode,
                               msat_make_number(menv, "1"))

    @property
    def correct1(self):
        """Return formula that holds iff state is correct1"""
        menv = self.menv
        return msat_make_equal(menv, self.mode,
                               msat_make_number(menv, "2"))

    @property
    def x_correct1(self):
        """Return formula that holds iff next state is correct1"""
        menv = self.menv
        return msat_make_equal(menv, self.x_mode,
                               msat_make_number(menv, "2"))

    @property
    def correct2(self):
        """Return formula that holds iff state is correct2"""
        menv = self.menv
        return msat_make_equal(menv, self.mode,
                               msat_make_number(menv, "3"))

    @property
    def x_correct2(self):
        """Return formula that holds iff next state is correct2"""
        menv = self.menv
        return msat_make_equal(menv, self.x_mode,
                               msat_make_number(menv, "3"))

    @property
    def curr2next(self) -> dict:
        """ Return dictionary of current-next symbols"""
        return {self.mode: self.x_mode,
                self.cm: self.x_cm,
                self.x: self.x_x}

    @property
    def init(self):
        """Return formula representing the initial states"""
        menv = self.menv
        _0 = msat_make_number(menv, "0")
        return msat_make_and(menv,
                             msat_make_and(menv, self.waiting,
                                           msat_make_equal(menv, self.x, _0)),
                             msat_make_equal(menv, self.cm, _0))

    @property
    def invar(self):
        """Return formula representing the invariant"""
        menv = self.menv
        _0 = msat_make_number(menv, "0")
        lhs = msat_make_not(menv, self.waiting)
        rhs = msat_make_and(menv,
                            msat_make_equal(menv, self.delta, _0),
                            msat_make_equal(menv, self.x, _0))
        return msat_make_and(menv,
                             msat_make_impl(menv, lhs, rhs),
                             msat_make_impl(menv, self.waiting,
                                            msat_make_leq(menv, self.x, self.delay)))

    @property
    def x_invar(self):
        """Return formula representing the invariant"""
        menv = self.menv
        _0 = msat_make_number(menv, "0")
        lhs = msat_make_not(menv, self.x_waiting)
        rhs = msat_make_and(menv,
                            msat_make_equal(menv, self.x_delta, _0),
                            msat_make_equal(menv, self.x_x, _0))
        return msat_make_and(menv,
                             msat_make_impl(menv, lhs, rhs),
                             msat_make_impl(menv, self.x_waiting,
                                            msat_make_leq(menv, self.x_x,
                                                          self.delay)))

    @property
    def trans(self):
        """Returns formula representing the transition relation"""
        menv = self.menv
        _0 = msat_make_number(menv, "0")
        d_eq_0 = msat_make_equal(menv, self.delta, _0)
        lhs = msat_make_gt(menv, self.delta, _0)
        rhs = msat_make_and(
            menv,
            msat_make_equal(menv, self.x_x,
                            msat_make_plus(menv, self.x, self.delta)),
            msat_make_equal(menv, self.x_mode, self.mode))
        res = msat_make_impl(menv, lhs, rhs)
        lhs = msat_make_and(menv, d_eq_0, self.waiting)
        rhs = self.x_receive
        res = msat_make_and(menv, res, msat_make_impl(menv, lhs, rhs))
        lhs = msat_make_and(menv, d_eq_0, self.receive)
        rhs = self.x_correct1
        res = msat_make_and(menv, res, msat_make_impl(menv, lhs, rhs))
        lhs = msat_make_and(menv, d_eq_0, self.correct1)
        rhs = self.x_correct2
        res = msat_make_and(menv, res, msat_make_impl(menv, lhs, rhs))
        lhs = msat_make_and(menv, d_eq_0, self.correct2)
        rhs = self.x_waiting
        res = msat_make_and(menv, res, msat_make_impl(menv, lhs, rhs))
        # guards and resets
        lhs = msat_make_and(menv, self.waiting, self.x_receive)
        rhs = msat_make_and(menv,
                            msat_make_geq(menv, self.x, self.delay),
                            msat_make_equal(menv, self.x_x, _0))
        res = msat_make_and(menv, res, msat_make_impl(menv, lhs, rhs))
        lhs = msat_make_not(menv, msat_make_and(menv, self.receive,
                                                self.x_correct1))
        rhs = msat_make_equal(menv, self.x_cm, self.cm)
        res = msat_make_and(menv, res, msat_make_impl(menv, lhs, rhs))
        return res


class SyncMaster:
    """Transition system describing a SyncMaster"""
    def __init__(self, menv: msat_env, name: str, drift,
                 delta, x_delta):
        self.menv = menv
        self.name = name
        self.drift = drift
        self.delta = delta
        self.x_delta = x_delta

        int_type = msat_get_integer_type(menv)
        real_type = msat_get_rational_type(menv)
        self.mode, self.x_mode = decl_consts(menv, "{}_mode".format(name),
                                             int_type)
        self.sm, self.x_sm = decl_consts(menv, "{}_sm".format(name), real_type)

    @property
    def work(self):
        """Return formula that holds iff state is work"""
        menv = self.menv
        return msat_make_equal(menv, self.mode, msat_make_number(menv, "0"))

    @property
    def x_work(self):
        """Return formula that holds iff next state is work"""
        menv = self.menv
        return msat_make_equal(menv, self.x_mode, msat_make_number(menv, "0"))

    @property
    def send(self):
        """Return formula that holds iff state is send"""
        menv = self.menv
        return msat_make_equal(menv, self.mode, msat_make_number(menv, "1"))

    @property
    def x_send(self):
        """Return formula that holds iff next state is send"""
        menv = self.menv
        return msat_make_equal(menv, self.x_mode, msat_make_number(menv, "1"))

    @property
    def sync1(self):
        """Return formula that holds iff state is sync1"""
        menv = self.menv
        return msat_make_equal(menv, self.mode, msat_make_number(menv, "2"))

    @property
    def x_sync1(self):
        """Return formula that holds iff next state is sync1"""
        menv = self.menv
        return msat_make_equal(menv, self.x_mode, msat_make_number(menv, "2"))

    @property
    def sync2(self):
        """Return formula that holds iff state is sync2"""
        menv = self.menv
        return msat_make_equal(menv, self.mode, msat_make_number(menv, "3"))

    @property
    def x_sync2(self):
        """Return formula that holds iff next state is sync2"""
        menv = self.menv
        return msat_make_equal(menv, self.x_mode, msat_make_number(menv, "3"))

    @property
    def curr2next(self) -> dict:
        """ Return dictionary of current-next symbols"""
        return {self.mode: self.x_mode, self.sm: self.x_sm}

    @property
    def init(self):
        """Return formula representing the initial states"""
        menv = self.menv
        _0 = msat_make_number(menv, "0")
        return msat_make_and(menv,
                             msat_make_equal(menv, self.sm, _0),
                             self.work)

    @property
    def invar(self):
        """Return formula representing the invariant"""
        return msat_make_true(self.menv)

    @property
    def x_invar(self):
        """Return formula representing the invariant"""
        return msat_make_true(self.menv)

    @property
    def trans(self):
        """Returns formula representing the transition relation"""
        menv = self.menv
        _0 = msat_make_number(menv, "0")
        d_eq_0 = msat_make_equal(menv, self.delta, _0)
        rhs = msat_make_and(menv,
                            msat_make_equal(menv, self.x_sm,
                                            msat_make_plus(menv, self.sm,
                                                           self.delta)),
                            msat_make_equal(menv, self.x_mode, self.mode))
        res = msat_make_impl(menv, msat_make_gt(menv, self.delta, _0), rhs)
        lhs = msat_make_and(menv, d_eq_0, self.work)
        rhs = self.x_send
        res = msat_make_and(menv, res, msat_make_impl(menv, lhs, rhs))
        lhs = msat_make_and(menv, d_eq_0, self.send)
        rhs = self.x_sync1
        res = msat_make_and(menv, res, msat_make_impl(menv, lhs, rhs))
        lhs = msat_make_and(menv, d_eq_0, self.sync1)
        rhs = self.x_sync2
        res = msat_make_and(menv, res, msat_make_impl(menv, lhs, rhs))
        lhs = msat_make_and(menv, d_eq_0, self.sync2)
        rhs = self.x_work
        res = msat_make_and(menv, res, msat_make_impl(menv, lhs, rhs))
        # guards and resets
        lhs = msat_make_and(menv, self.work, self.x_send)
        rhs = msat_make_and(menv,
                            msat_make_leq(menv,
                                          msat_make_minus(menv, self.sm,
                                                          self.drift),
                                          self.x_sm),
                            msat_make_leq(menv, self.x_sm,
                                          msat_make_plus(menv, self.sm,
                                                         self.drift)))
        res = msat_make_and(menv, res, msat_make_impl(menv, lhs, rhs))
        lhs = msat_make_or(
            menv,
            msat_make_and(menv, self.send, self.x_sync1),
            msat_make_or(menv,
                         msat_make_and(menv, self.sync1, self.x_sync2),
                         msat_make_and(menv, self.sync2, self.x_work)))
        rhs = msat_make_equal(menv, self.x_sm, self.sm)
        res = msat_make_and(menv, res, msat_make_impl(menv, lhs, rhs))
        return res


def sync_comprmaster_syncmaster(menv: msat_env, cm: ComprMaster,
                                sm: SyncMaster):
    """Synchronise ComprMaster with SyncMaster on discrete transitions"""
    res = msat_make_iff(menv,
                        msat_make_and(menv, cm.waiting, cm.x_receive),
                        msat_make_and(menv, sm.work, sm.x_send))
    curr = msat_make_iff(menv,
                         msat_make_and(menv, cm.receive, cm.x_correct1),
                         msat_make_and(menv, sm.send, sm.x_sync1))
    res = msat_make_and(menv, res, curr)
    curr = msat_make_iff(menv,
                         msat_make_and(menv, cm.correct1, cm.x_correct2),
                         msat_make_and(menv, sm.sync1, sm.x_sync2))
    res = msat_make_and(menv, res, curr)
    curr = msat_make_iff(menv,
                         msat_make_and(menv, cm.correct2, cm.x_waiting),
                         msat_make_and(menv, sm.sync2, sm.x_work))
    res = msat_make_and(menv, res, curr)
    return res


def sync_on_broadcast_messages(menv: msat_env, cms: list,
                               sms: list):
    """synchronisation of clocks on broadcast messages"""
    n_cms = msat_make_number(menv, str(len(cms)))
    n_sms = msat_make_number(menv, str(len(sms)))
    sm_val = cms[0].cm
    for cm in cms[1:]:
        sm_val = msat_make_plus(menv, sm_val, cm.cm)
    sm_val = msat_make_divide(menv, sm_val, n_cms)
    cm_val = sms[0].sm
    for sm in sms[1:]:
        cm_val = msat_make_plus(menv, cm_val, sm.sm)
    cm_val = msat_make_divide(menv, cm_val, n_sms)
    sm = sms[0]
    lhs = msat_make_and(menv, sm.sync1, sm.x_sync2)
    rhs = msat_make_equal(menv, sm.x_sm, sm_val)
    curr = msat_make_impl(menv, lhs, rhs)
    for sm in sms[1:]:
        lhs = msat_make_and(menv, sm.sync1, sm.x_sync2)
        rhs = msat_make_equal(menv, sm.x_sm, sm_val)
        curr = msat_make_and(menv, curr, msat_make_impl(menv, lhs, rhs))
    res = curr
    cm = cms[0]
    lhs = msat_make_and(menv, cm.receive, cm.x_correct1)
    rhs = msat_make_equal(menv, cm.x_cm, cm_val)
    curr = msat_make_impl(menv, lhs, rhs)
    for cm in cms[1:]:
        lhs = msat_make_and(menv, cm.receive, cm.x_correct1)
        rhs = msat_make_equal(menv, cm.x_cm, cm_val)
        curr = msat_make_and(menv, curr, msat_make_impl(menv, lhs, rhs))
    res = msat_make_and(menv, res, curr)
    return res
