//@ ltl invariant negative: ( ([] ( (<> AP((device_exploded != 0))) || (! AP((collision != 0))))) || (! ( ([] ( (! ( AP((fault_corruption != 0)) || AP((fault_deletion != 0)))) || (! ( (X AP((fault_deletion != 0))) || (X AP((fault_corruption != 0))))))) && AP((2 <= max_delta_counter_init)))));

extern int __VERIFIER_nondet_int(void);

char __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}


int max_delta_counter_init, _x_max_delta_counter_init;
char new_valid_data, _x_new_valid_data;
int sensor_counter, _x_sensor_counter;
int link_out_message, _x_link_out_message;
int sensor_message, _x_sensor_message;
int link_out_counter, _x_link_out_counter;
char link_valid_crc, _x_link_valid_crc;
char link_new_data_available, _x_link_new_data_available;
int device_last_valid_counter, _x_device_last_valid_counter;
char device_exploded, _x_device_exploded;
char collision, _x_collision;
char fault_deletion, _x_fault_deletion;
char fault_corruption, _x_fault_corruption;

int main()
{
  max_delta_counter_init = __VERIFIER_nondet_int();
  new_valid_data = __VERIFIER_nondet_bool();
  sensor_counter = __VERIFIER_nondet_int();
  link_out_message = __VERIFIER_nondet_int();
  sensor_message = __VERIFIER_nondet_int();
  link_out_counter = __VERIFIER_nondet_int();
  link_valid_crc = __VERIFIER_nondet_bool();
  link_new_data_available = __VERIFIER_nondet_bool();
  device_last_valid_counter = __VERIFIER_nondet_int();
  device_exploded = __VERIFIER_nondet_bool();
  collision = __VERIFIER_nondet_bool();
  fault_deletion = __VERIFIER_nondet_bool();
  fault_corruption = __VERIFIER_nondet_bool();

  int __ok = (((((sensor_message == 2) && ( !(link_new_data_available != 0))) && ( !(link_valid_crc != 0))) && ((new_valid_data != 0) == ((link_new_data_available != 0) && (link_valid_crc != 0)))) && ((sensor_message == 2) || ((sensor_message == 0) || (sensor_message == 1))));
  while (__ok) {
    _x_max_delta_counter_init = __VERIFIER_nondet_int();
    _x_new_valid_data = __VERIFIER_nondet_bool();
    _x_sensor_counter = __VERIFIER_nondet_int();
    _x_link_out_message = __VERIFIER_nondet_int();
    _x_sensor_message = __VERIFIER_nondet_int();
    _x_link_out_counter = __VERIFIER_nondet_int();
    _x_link_valid_crc = __VERIFIER_nondet_bool();
    _x_link_new_data_available = __VERIFIER_nondet_bool();
    _x_device_last_valid_counter = __VERIFIER_nondet_int();
    _x_device_exploded = __VERIFIER_nondet_bool();
    _x_collision = __VERIFIER_nondet_bool();
    _x_fault_deletion = __VERIFIER_nondet_bool();
    _x_fault_corruption = __VERIFIER_nondet_bool();

    __ok = (((_x_device_exploded != 0) || ( !(((((_x_link_valid_crc != 0) && ((_x_link_new_data_available != 0) && (new_valid_data != 0))) && (_x_link_out_message == 1)) && ((_x_device_last_valid_counter + (-1 * _x_link_out_counter)) <= -1)) && (-1 <= (_x_device_last_valid_counter + ((-1 * _x_link_out_counter) + max_delta_counter_init)))))) && (((_x_device_exploded != 0) || ( !(device_exploded != 0))) && (((_x_new_valid_data != 0) == ((new_valid_data != 0) || ((_x_link_new_data_available != 0) && (_x_link_valid_crc != 0)))) && ((( !(fault_corruption != 0)) || ( !(_x_link_valid_crc != 0))) && ((( !(fault_deletion != 0)) || ( !(_x_link_new_data_available != 0))) && ((((link_new_data_available != 0) && (link_valid_crc != 0)) || (device_last_valid_counter == _x_device_last_valid_counter)) && (((_x_device_last_valid_counter == link_out_counter) || (device_last_valid_counter == _x_device_last_valid_counter)) && (((fault_corruption != 0) || (_x_link_valid_crc != 0)) && (((fault_deletion != 0) || ((((_x_link_new_data_available != 0) == ( !(sensor_message == 2))) && (sensor_message == _x_link_out_message)) && (_x_link_out_counter == sensor_counter))) && ((( !(sensor_message == 2)) || (sensor_counter == _x_sensor_counter)) && (((sensor_message == 2) || ((sensor_counter + (-1 * _x_sensor_counter)) == -1)) && (((collision != 0) == (_x_sensor_message == 1)) && ((max_delta_counter_init == _x_max_delta_counter_init) && (((_x_sensor_message == 0) || (_x_sensor_message == 1)) || (_x_sensor_message == 2)))))))))))))));
    max_delta_counter_init = _x_max_delta_counter_init;
    new_valid_data = _x_new_valid_data;
    sensor_counter = _x_sensor_counter;
    link_out_message = _x_link_out_message;
    sensor_message = _x_sensor_message;
    link_out_counter = _x_link_out_counter;
    link_valid_crc = _x_link_valid_crc;
    link_new_data_available = _x_link_new_data_available;
    device_last_valid_counter = _x_device_last_valid_counter;
    device_exploded = _x_device_exploded;
    collision = _x_collision;
    fault_deletion = _x_fault_deletion;
    fault_corruption = _x_fault_corruption;

  }
}
