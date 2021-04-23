//@ ltl invariant negative: ( ([] ( AP((o_collision != 0)) || (! AP((device_exploded != 0))))) || (! ([] (<> (! AP((sensor_message == 2)))))));

extern int __VERIFIER_nondet_int(void);

char __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}


int sensor_counter, _x_sensor_counter;
int link_out_message, _x_link_out_message;
int sensor_message, _x_sensor_message;
int link_out_counter, _x_link_out_counter;
char link_valid_crc, _x_link_valid_crc;
char link_new_data_available, _x_link_new_data_available;
char device_exploded, _x_device_exploded;
char o_valid_explode, _x_o_valid_explode;
char o_collision, _x_o_collision;
char fault_deletion, _x_fault_deletion;
char fault_corruption, _x_fault_corruption;

int main()
{
  sensor_counter = __VERIFIER_nondet_int();
  link_out_message = __VERIFIER_nondet_int();
  sensor_message = __VERIFIER_nondet_int();
  link_out_counter = __VERIFIER_nondet_int();
  link_valid_crc = __VERIFIER_nondet_bool();
  link_new_data_available = __VERIFIER_nondet_bool();
  device_exploded = __VERIFIER_nondet_bool();
  o_valid_explode = __VERIFIER_nondet_bool();
  o_collision = __VERIFIER_nondet_bool();
  fault_deletion = __VERIFIER_nondet_bool();
  fault_corruption = __VERIFIER_nondet_bool();

  int __ok = ((((link_new_data_available != 0) && (link_valid_crc != 0)) && (link_out_message == 1)) && ((sensor_message == 2) || ((sensor_message == 0) || (sensor_message == 1))));
  while (__ok) {
    _x_sensor_counter = __VERIFIER_nondet_int();
    _x_link_out_message = __VERIFIER_nondet_int();
    _x_sensor_message = __VERIFIER_nondet_int();
    _x_link_out_counter = __VERIFIER_nondet_int();
    _x_link_valid_crc = __VERIFIER_nondet_bool();
    _x_link_new_data_available = __VERIFIER_nondet_bool();
    _x_device_exploded = __VERIFIER_nondet_bool();
    _x_o_valid_explode = __VERIFIER_nondet_bool();
    _x_o_collision = __VERIFIER_nondet_bool();
    _x_fault_deletion = __VERIFIER_nondet_bool();
    _x_fault_corruption = __VERIFIER_nondet_bool();

    __ok = (((_x_device_exploded != 0) || ( !(device_exploded != 0))) && (((_x_o_valid_explode != 0) == ((o_valid_explode != 0) || (((_x_link_new_data_available != 0) && (_x_link_valid_crc != 0)) && (_x_link_out_message == 1)))) && ((( !(fault_corruption != 0)) || ( !(_x_link_valid_crc != 0))) && (((fault_corruption != 0) || (_x_link_valid_crc != 0)) && ((( !(fault_deletion != 0)) || ( !(_x_link_new_data_available != 0))) && (((fault_deletion != 0) || ((((_x_link_new_data_available != 0) == ( !(sensor_message == 2))) && (sensor_message == _x_link_out_message)) && (_x_link_out_counter == sensor_counter))) && ((( !(sensor_message == 2)) || (sensor_counter == _x_sensor_counter)) && (((sensor_message == 2) || ((sensor_counter + (-1 * _x_sensor_counter)) == -1)) && ((((_x_sensor_message == 0) || (_x_sensor_message == 1)) || (_x_sensor_message == 2)) && ((o_collision != 0) == ((o_collision != 0) || (_x_sensor_message == 1))))))))))));
    sensor_counter = _x_sensor_counter;
    link_out_message = _x_link_out_message;
    sensor_message = _x_sensor_message;
    link_out_counter = _x_link_out_counter;
    link_valid_crc = _x_link_valid_crc;
    link_new_data_available = _x_link_new_data_available;
    device_exploded = _x_device_exploded;
    o_valid_explode = _x_o_valid_explode;
    o_collision = _x_o_collision;
    fault_deletion = _x_fault_deletion;
    fault_corruption = _x_fault_corruption;

  }
}
