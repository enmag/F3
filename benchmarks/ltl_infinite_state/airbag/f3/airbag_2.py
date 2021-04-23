from collections import Iterable
from mathsat import msat_term, msat_env
from mathsat import msat_make_constant, msat_declare_function
from mathsat import msat_get_integer_type, msat_get_bool_type
from mathsat import msat_make_and, msat_make_not, msat_make_or, msat_make_iff
from mathsat import msat_make_leq, msat_make_equal
from mathsat import msat_make_number, msat_make_plus, msat_make_times
from ltl.ltl import TermMap, LTLEncoder
from utils import name_next


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
    bool_type = msat_get_bool_type(menv)

    curr2next = {}
    name = "fault_corruption"
    fault_corruption = msat_declare_function(menv, name, bool_type)
    fault_corruption = msat_make_constant(menv, fault_corruption)
    x_fault_corruption = msat_declare_function(menv, name_next(name),
                                               bool_type)
    x_fault_corruption = msat_make_constant(menv, x_fault_corruption)
    curr2next[fault_corruption] = x_fault_corruption

    name = "fault_deletion"
    fault_deletion = msat_declare_function(menv, name, bool_type)
    fault_deletion = msat_make_constant(menv, fault_deletion)
    x_fault_deletion = msat_declare_function(menv, name_next(name),
                                             bool_type)
    x_fault_deletion = msat_make_constant(menv, x_fault_deletion)
    curr2next[fault_deletion] = x_fault_deletion

    name = "o_collision"
    o_collision = msat_declare_function(menv, name, bool_type)
    o_collision = msat_make_constant(menv, o_collision)
    x_o_collision = msat_declare_function(menv, name_next(name),
                                          bool_type)
    x_o_collision = msat_make_constant(menv, x_o_collision)
    curr2next[o_collision] = x_o_collision

    name = "o_valid_explode"
    o_explode = msat_declare_function(menv, name, bool_type)
    o_explode = msat_make_constant(menv, o_explode)
    x_o_explode = msat_declare_function(menv, name_next(name),
                                        bool_type)
    x_o_explode = msat_make_constant(menv, x_o_explode)
    curr2next[o_explode] = x_o_explode

    name = "device_exploded"
    exploded = msat_declare_function(menv, name, bool_type)
    exploded = msat_make_constant(menv, exploded)
    x_exploded = msat_declare_function(menv, name_next(name),
                                       bool_type)
    x_exploded = msat_make_constant(menv, x_exploded)
    curr2next[exploded] = x_exploded

    name = "link_new_data_available"
    new_data = msat_declare_function(menv, name, bool_type)
    new_data = msat_make_constant(menv, new_data)
    x_new_data = msat_declare_function(menv, name_next(name),
                                       bool_type)
    x_new_data = msat_make_constant(menv, x_new_data)
    curr2next[new_data] = x_new_data

    name = "link_valid_crc"
    valid_crc = msat_declare_function(menv, name, bool_type)
    valid_crc = msat_make_constant(menv, valid_crc)
    x_valid_crc = msat_declare_function(menv, name_next(name),
                                        bool_type)
    x_valid_crc = msat_make_constant(menv, x_valid_crc)
    curr2next[valid_crc] = x_valid_crc

    name = "link_out_counter"
    out_count = msat_declare_function(menv, name, int_type)
    out_count = msat_make_constant(menv, out_count)
    x_out_count = msat_declare_function(menv, name_next(name),
                                        int_type)
    x_out_count = msat_make_constant(menv, x_out_count)
    curr2next[out_count] = x_out_count

    name = "sensor_message"
    msg = msat_declare_function(menv, name, int_type)
    msg = msat_make_constant(menv, msg)
    x_msg = msat_declare_function(menv, name_next(name),
                                  int_type)
    x_msg = msat_make_constant(menv, x_msg)
    curr2next[msg] = x_msg

    name = "link_out_message"
    out_msg = msat_declare_function(menv, name, int_type)
    out_msg = msat_make_constant(menv, out_msg)
    x_out_msg = msat_declare_function(menv, name_next(name),
                                      int_type)
    x_out_msg = msat_make_constant(menv, x_out_msg)
    curr2next[out_msg] = x_out_msg

    name = "sensor_counter"
    count = msat_declare_function(menv, name, int_type)
    count = msat_make_constant(menv, count)
    x_count = msat_declare_function(menv, name_next(name),
                                    int_type)
    x_count = msat_make_constant(menv, x_count)
    curr2next[count] = x_count

    one = msat_make_number(menv, "1")
    two = msat_make_number(menv, "2")
    msg_other = msat_make_number(menv, "0")
    msg_explode = one
    msg_no = two

    # sensor.message = no_message
    init = msat_make_equal(menv, msg, msg_no)
    # !link.NewDataAvailable
    init = msat_make_and(menv, init, msat_make_not(menv, new_data))
    # O_validExplode <-> (link.NewDataAvailable & link.ValidCRC & link.out_message = explode);
    init = msat_make_and(menv, new_data, valid_crc)
    init = msat_make_and(menv, init,
                         msat_make_equal(menv, out_msg, msg_explode))

    t = msat_make_equal(menv, msg, msg_other)
    t = msat_make_or(menv, t, msat_make_equal(menv, msg, msg_explode))
    t = msat_make_or(menv, t, msat_make_equal(menv, msg, msg_no))
    init = msat_make_and(menv, init, t)

    trans = []
    # msg in {msg_other, msg_explode, msg_no}
    t = msat_make_equal(menv, x_msg, msg_other)
    t = msat_make_or(menv, t, msat_make_equal(menv, x_msg, msg_explode))
    t = msat_make_or(menv, t, msat_make_equal(menv, x_msg, msg_no))
    trans.append(t)

    # O_collision <-> (O_collision | sensor.message' = explode)
    trans.append(msat_make_iff(menv, o_collision,
                               msat_make_or(menv, o_collision,
                                            msat_make_equal(menv, x_msg,
                                                            msg_explode))))
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
    # link.NewDataAvailable' ->  !fault_deletion
    trans.append(msat_make_impl(menv, x_new_data,
                                msat_make_not(menv, fault_deletion)))
    # !fault_corruption -> link.ValidCRC'
    trans.append(msat_make_impl(menv, msat_make_not(menv, fault_corruption),
                                x_valid_crc))
    # valid_crc' -> ! fault_corruption
    trans.append(msat_make_impl(menv, x_valid_crc,
                                msat_make_not(menv, fault_corruption)))
    # O_validExplode' <-> O_validExplode |
    # (link.NewDataAvailable' & link.ValidCRC' & link.out_message' = explode)
    curr = msat_make_and(menv, x_new_data, x_valid_crc)
    curr = msat_make_and(menv, curr,
                         msat_make_equal(menv, x_out_msg, msg_explode))
    curr = msat_make_or(menv, o_explode, curr)
    curr = msat_make_iff(menv, x_o_explode, curr)
    trans.append(curr)
    # device.exploded -> next(device.exploded)
    trans.append(msat_make_impl(menv, exploded, x_exploded))

    _trans = trans[0]
    for t in trans[1:]:
        _trans = msat_make_and(menv, _trans, t)
    trans = _trans

    # (G F sensor.message != no_message) -> G (device.exploded -> O_collision)
    lhs = msat_make_not(menv, msat_make_equal(menv, msg, msg_no))
    lhs = enc.make_G(enc.make_F(lhs))
    rhs = enc.make_G(msat_make_impl(menv, exploded, o_collision))
    ltl = msat_make_impl(menv, lhs, rhs)

    return TermMap(curr2next), init, trans, ltl
