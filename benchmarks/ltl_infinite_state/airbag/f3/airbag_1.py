from typing import Iterable, Tuple
from mathsat import msat_term, msat_env
from mathsat import msat_make_constant, msat_declare_function
from mathsat import msat_get_integer_type, msat_get_bool_type
from mathsat import msat_make_and, msat_make_not, msat_make_or, msat_make_iff
from mathsat import msat_make_leq, msat_make_equal
from mathsat import msat_make_number, msat_make_plus, msat_make_times
from ltl.ltl import TermMap, LTLEncoder
from expr_utils import name2next

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


def check_ltl(menv: msat_env, enc: LTLEncoder) -> Tuple[Iterable, msat_term,
                                                        msat_term, msat_term]:
    assert menv
    assert isinstance(menv, msat_env)
    assert enc
    assert isinstance(enc, LTLEncoder)
    int_type = msat_get_integer_type(menv)
    bool_type = msat_get_bool_type(menv)

    curr2next = {}
    name = "fault_corruption"
    fault_corruption = msat_declare_function(menv, name, bool_type)
    fault_corruption = msat_make_constant(menv, fault_corruption)
    x_fault_corruption = msat_declare_function(menv, name2next(name),
                                               bool_type)
    x_fault_corruption = msat_make_constant(menv, x_fault_corruption)
    curr2next[fault_corruption] = x_fault_corruption

    name = "fault_deletion"
    fault_deletion = msat_declare_function(menv, name, bool_type)
    fault_deletion = msat_make_constant(menv, fault_deletion)
    x_fault_deletion = msat_declare_function(menv, name2next(name),
                                             bool_type)
    x_fault_deletion = msat_make_constant(menv, x_fault_deletion)
    curr2next[fault_deletion] = x_fault_deletion

    name = "collision"
    collision = msat_declare_function(menv, name, bool_type)
    collision = msat_make_constant(menv, collision)
    x_collision = msat_declare_function(menv, name2next(name),
                                        bool_type)
    x_collision = msat_make_constant(menv, x_collision)
    curr2next[collision] = x_collision

    name = "device_exploded"
    exploded = msat_declare_function(menv, name, bool_type)
    exploded = msat_make_constant(menv, exploded)
    x_exploded = msat_declare_function(menv, name2next(name),
                                       bool_type)
    x_exploded = msat_make_constant(menv, x_exploded)
    curr2next[exploded] = x_exploded

    name = "device_last_valid_counter"
    last_valid_count = msat_declare_function(menv, name, int_type)
    last_valid_count = msat_make_constant(menv, last_valid_count)
    x_last_valid_count = msat_declare_function(menv, name2next(name),
                                               int_type)
    x_last_valid_count = msat_make_constant(menv, x_last_valid_count)
    curr2next[last_valid_count] = x_last_valid_count

    name = "link_new_data_available"
    new_data = msat_declare_function(menv, name, bool_type)
    new_data = msat_make_constant(menv, new_data)
    x_new_data = msat_declare_function(menv, name2next(name),
                                       bool_type)
    x_new_data = msat_make_constant(menv, x_new_data)
    curr2next[new_data] = x_new_data

    name = "link_valid_crc"
    valid_crc = msat_declare_function(menv, name, bool_type)
    valid_crc = msat_make_constant(menv, valid_crc)
    x_valid_crc = msat_declare_function(menv, name2next(name),
                                        bool_type)
    x_valid_crc = msat_make_constant(menv, x_valid_crc)
    curr2next[valid_crc] = x_valid_crc

    name = "link_out_counter"
    out_count = msat_declare_function(menv, name, int_type)
    out_count = msat_make_constant(menv, out_count)
    x_out_count = msat_declare_function(menv, name2next(name),
                                        int_type)
    x_out_count = msat_make_constant(menv, x_out_count)
    curr2next[out_count] = x_out_count

    name = "sensor_message"
    msg = msat_declare_function(menv, name, int_type)
    msg = msat_make_constant(menv, msg)
    x_msg = msat_declare_function(menv, name2next(name),
                                  int_type)
    x_msg = msat_make_constant(menv, x_msg)
    curr2next[msg] = x_msg

    name = "link_out_message"
    out_msg = msat_declare_function(menv, name, int_type)
    out_msg = msat_make_constant(menv, out_msg)
    x_out_msg = msat_declare_function(menv, name2next(name),
                                      int_type)
    x_out_msg = msat_make_constant(menv, x_out_msg)
    curr2next[out_msg] = x_out_msg

    name = "sensor_counter"
    count = msat_declare_function(menv, name, int_type)
    count = msat_make_constant(menv, count)
    x_count = msat_declare_function(menv, name2next(name),
                                    int_type)
    x_count = msat_make_constant(menv, x_count)
    curr2next[count] = x_count

    name = "new_valid_data"
    val_data = msat_declare_function(menv, name, bool_type)
    val_data = msat_make_constant(menv, val_data)
    x_val_data = msat_declare_function(menv, name2next(name),
                                       bool_type)
    x_val_data = msat_make_constant(menv, x_val_data)
    curr2next[val_data] = x_val_data
    name = "max_delta_counter_init"
    max_delta = msat_declare_function(menv, name, int_type)
    max_delta = msat_make_constant(menv, max_delta)
    x_max_delta = msat_declare_function(menv, name2next(name),
                                        int_type)
    x_max_delta = msat_make_constant(menv, x_max_delta)
    curr2next[max_delta] = x_max_delta

    one = msat_make_number(menv, "1")
    two = msat_make_number(menv, "2")
    msg_other = msat_make_number(menv, "0")
    msg_explode = one
    msg_no = two

    # sensor.message = no_message
    init = msat_make_equal(menv, msg, msg_no)
    # !link.NewDataAvailable
    init = msat_make_and(menv, init, msat_make_not(menv, new_data))
    # !link.ValidCRC
    init = msat_make_and(menv, init, msat_make_not(menv, valid_crc))
    # newValidData <-> link.NewDataAvailable & link.ValidCRC
    init = msat_make_and(menv, init, msat_make_iff(menv, val_data,
                                                   msat_make_and(menv,
                                                                 new_data,
                                                                 valid_crc)))
    t = msat_make_equal(menv, msg, msg_other)
    t = msat_make_or(menv, t, msat_make_equal(menv, msg, msg_explode))
    t = msat_make_or(menv, t, msat_make_equal(menv, msg, msg_no))
    init = msat_make_and(menv, init, t)

    # frozenvar
    trans = [msat_make_equal(menv, x_max_delta, max_delta)]
    # msg in {msg_other, msg_explode, msg_no}
    t = msat_make_equal(menv, x_msg, msg_other)
    t = msat_make_or(menv, t, msat_make_equal(menv, x_msg, msg_explode))
    t = msat_make_or(menv, t, msat_make_equal(menv, x_msg, msg_no))
    trans.append(t)

    # collision <-> next(sensor.message) = explode
    trans.append(msat_make_iff(menv, collision,
                               msat_make_equal(menv, x_msg, msg_explode)))
    # sensor.message != no_message -> sensor.Counter' = (sensor.Counter + 1)
    not_msg_no = msat_make_not(menv, msat_make_equal(menv, msg, msg_no))
    trans.append(msat_make_impl(menv, not_msg_no,
                                msat_make_equal(menv, x_count,
                                                msat_make_plus(menv, count,
                                                               one))))
    # sensor.message = no_message -> sensor.Counter' = sensor.Counter
    trans.append(msat_make_impl(menv, msat_make_equal(menv, msg, msg_no),
                                msat_make_equal(menv, x_count, count)))
    # !fault_deletion -> ((link.NewDataAvailable' <-> sensor.message != no_message) &
    #                      link.out_message' = sensor.message &
    #                      link.out_Counter' = sensor.Counter)
    rhs = msat_make_iff(menv, x_new_data, not_msg_no)
    rhs = msat_make_and(menv, rhs, msat_make_equal(menv, x_out_msg, msg))
    rhs = msat_make_and(menv, rhs, msat_make_equal(menv, x_out_count, count))
    trans.append(msat_make_impl(menv, msat_make_not(menv, fault_deletion),
                                rhs))
    # !fault_corruption -> link.ValidCRC'
    trans.append(msat_make_impl(menv, msat_make_not(menv, fault_corruption),
                                x_valid_crc))
    # device.LastValidCounter' = link.out_Counter |
    # device.LastValidCounter' = device.LastValidCounter
    eq0 = msat_make_equal(menv, x_last_valid_count, out_count)
    eq1 = msat_make_equal(menv, x_last_valid_count, last_valid_count)
    curr_t = msat_make_or(menv, eq0, eq1)
    trans.append(curr_t)
    # device.LastValidCounter' != device.LastValidCounter ->
    # (link.NewDataAvailable & link.ValidCRC)
    trans.append(msat_make_impl(
        menv,
        msat_make_not(menv,
                      msat_make_equal(menv,
                                      x_last_valid_count,
                                      last_valid_count)),
        msat_make_and(menv, new_data, valid_crc)))
    # link.NewDataAvailable' ->  !fault_deletion
    trans.append(msat_make_impl(menv, x_new_data,
                                msat_make_not(menv, fault_deletion)))
    # link.ValidCRC' -> !fault_corruption
    trans.append(msat_make_impl(menv, x_valid_crc,
                                msat_make_not(menv, fault_corruption)))
    # newValidData' <-> (newValidData | (link.NewDataAvailable' & link.ValidCRC'))
    rhs = msat_make_or(menv, val_data,
                       msat_make_and(menv, x_new_data, x_valid_crc))
    trans.append(msat_make_iff(menv, x_val_data, rhs))
    # device.exploded -> next(device.exploded)
    trans.append(msat_make_impl(menv, exploded, x_exploded))
    # (newValidData &
    # link.NewDataAvailable' & link.ValidCRC' & link.out_message' = explode &
    # link.out_Counter' - device.LastValidCounter'  >= 1 &
    # link.out_Counter' - device.LastValidCounter'  <= MaxDeltaCounterInit + 1)
    # -> device.exploded';
    lhs = val_data
    lhs = msat_make_and(menv, lhs, x_new_data)
    lhs = msat_make_and(menv, lhs, x_valid_crc)
    lhs = msat_make_and(menv, lhs,
                        msat_make_equal(menv, x_out_msg, msg_explode))
    lhs = msat_make_and(menv, lhs,
                        msat_make_geq(menv,
                                      msat_make_minus(menv, x_out_count,
                                                      x_last_valid_count),
                                      one))
    lhs = msat_make_and(menv, lhs,
                        msat_make_leq(
                            menv,
                            msat_make_minus(menv, x_out_count,
                                            x_last_valid_count),
                            msat_make_plus(menv, max_delta, one)))
    trans.append(msat_make_impl(menv, lhs, x_exploded))

    _trans = trans[0]
    for t in trans[1:]:
        _trans = msat_make_and(menv, _trans, t)
    trans = _trans

    # (G F sensor.message != no_message) ->
    # (MaxDeltaCounterInit >= 2 &
    # G (((fault_corruption | fault_deletion) ->  X !(fault_corruption | fault_deletion)))
    # ) -> G (collision -> F device.exploded)
    disj = msat_make_or(menv, fault_corruption, fault_deletion)
    lhs = msat_make_impl(menv, disj, enc.make_X(msat_make_not(menv, disj)))
    lhs = enc.make_G(lhs)
    lhs = msat_make_and(menv, msat_make_geq(menv, max_delta, two), lhs)
    rhs = msat_make_impl(menv, collision, enc.make_F(exploded))
    rhs = enc.make_G(rhs)
    ltl = msat_make_impl(menv, lhs, rhs)

    return TermMap(curr2next), init, trans, ltl
