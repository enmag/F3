extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);
typedef enum {false, true} bool;
bool __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}

int main()
{
int sensor_message, _x_sensor_message;
bool link_valid_crc, _x_link_valid_crc;
bool link_new_data_available, _x_link_new_data_available;
bool new_valid_data, _x_new_valid_data;
bool _J192, _x__J192;
bool _J175, _x__J175;
bool _J165, _x__J165;
bool _EL_X_121, _x__EL_X_121;
bool _EL_X_122, _x__EL_X_122;
bool fault_deletion, _x_fault_deletion;
bool fault_corruption, _x_fault_corruption;
bool _EL_U_137, _x__EL_U_137;
int max_delta_counter_init, _x_max_delta_counter_init;
bool _EL_U_141, _x__EL_U_141;
bool device_exploded, _x_device_exploded;
bool collision, _x_collision;
bool _EL_U_144, _x__EL_U_144;
int link_out_message, _x_link_out_message;
int sensor_counter, _x_sensor_counter;
int device_last_valid_counter, _x_device_last_valid_counter;
int link_out_counter, _x_link_out_counter;

  int __steps_to_fair = __VERIFIER_nondet_int();
  sensor_message = __VERIFIER_nondet_int();
  link_valid_crc = __VERIFIER_nondet_bool();
  link_new_data_available = __VERIFIER_nondet_bool();
  new_valid_data = __VERIFIER_nondet_bool();
  _J192 = __VERIFIER_nondet_bool();
  _J175 = __VERIFIER_nondet_bool();
  _J165 = __VERIFIER_nondet_bool();
  _EL_X_121 = __VERIFIER_nondet_bool();
  _EL_X_122 = __VERIFIER_nondet_bool();
  fault_deletion = __VERIFIER_nondet_bool();
  fault_corruption = __VERIFIER_nondet_bool();
  _EL_U_137 = __VERIFIER_nondet_bool();
  max_delta_counter_init = __VERIFIER_nondet_int();
  _EL_U_141 = __VERIFIER_nondet_bool();
  device_exploded = __VERIFIER_nondet_bool();
  collision = __VERIFIER_nondet_bool();
  _EL_U_144 = __VERIFIER_nondet_bool();
  link_out_message = __VERIFIER_nondet_int();
  sensor_counter = __VERIFIER_nondet_int();
  device_last_valid_counter = __VERIFIER_nondet_int();
  link_out_counter = __VERIFIER_nondet_int();

  bool __ok = ((((((sensor_message == 2) && ( !link_new_data_available)) && ( !link_valid_crc)) && (new_valid_data == (link_new_data_available && link_valid_crc))) && ((sensor_message == 2) || ((sensor_message == 0) || (sensor_message == 1)))) && (((( !(( !(_EL_U_144 || ( !(( !collision) || (device_exploded || _EL_U_141))))) || ( !((2 <= max_delta_counter_init) && ( !(_EL_U_137 || ( !(( !(fault_corruption || fault_deletion)) || ( !(_EL_X_122 || _EL_X_121)))))))))) && ( !_J165)) && ( !_J175)) && ( !_J192)));
  while (__steps_to_fair >= 0 && __ok) {
    if (((_J165 && _J175) && _J192)) {
      __steps_to_fair = __VERIFIER_nondet_int();
    } else {
      __steps_to_fair--;
    }
    _x_sensor_message = __VERIFIER_nondet_int();
    _x_link_valid_crc = __VERIFIER_nondet_bool();
    _x_link_new_data_available = __VERIFIER_nondet_bool();
    _x_new_valid_data = __VERIFIER_nondet_bool();
    _x__J192 = __VERIFIER_nondet_bool();
    _x__J175 = __VERIFIER_nondet_bool();
    _x__J165 = __VERIFIER_nondet_bool();
    _x__EL_X_121 = __VERIFIER_nondet_bool();
    _x__EL_X_122 = __VERIFIER_nondet_bool();
    _x_fault_deletion = __VERIFIER_nondet_bool();
    _x_fault_corruption = __VERIFIER_nondet_bool();
    _x__EL_U_137 = __VERIFIER_nondet_bool();
    _x_max_delta_counter_init = __VERIFIER_nondet_int();
    _x__EL_U_141 = __VERIFIER_nondet_bool();
    _x_device_exploded = __VERIFIER_nondet_bool();
    _x_collision = __VERIFIER_nondet_bool();
    _x__EL_U_144 = __VERIFIER_nondet_bool();
    _x_link_out_message = __VERIFIER_nondet_int();
    _x_sensor_counter = __VERIFIER_nondet_int();
    _x_device_last_valid_counter = __VERIFIER_nondet_int();
    _x_link_out_counter = __VERIFIER_nondet_int();

    __ok = (((_x_device_exploded || ( !((((_x_link_valid_crc && (_x_link_new_data_available && new_valid_data)) && (_x_link_out_message == 1)) && ((_x_device_last_valid_counter + (-1 * _x_link_out_counter)) <= -1)) && (-1 <= (_x_device_last_valid_counter + ((-1 * _x_link_out_counter) + max_delta_counter_init)))))) && ((_x_device_exploded || ( !device_exploded)) && ((_x_new_valid_data == (new_valid_data || (_x_link_new_data_available && _x_link_valid_crc))) && ((( !fault_corruption) || ( !_x_link_valid_crc)) && ((( !fault_deletion) || ( !_x_link_new_data_available)) && (((link_new_data_available && link_valid_crc) || (device_last_valid_counter == _x_device_last_valid_counter)) && (((_x_device_last_valid_counter == link_out_counter) || (device_last_valid_counter == _x_device_last_valid_counter)) && ((fault_corruption || _x_link_valid_crc) && ((fault_deletion || (((_x_link_new_data_available == ( !(sensor_message == 2))) && (sensor_message == _x_link_out_message)) && (_x_link_out_counter == sensor_counter))) && ((( !(sensor_message == 2)) || (sensor_counter == _x_sensor_counter)) && (((sensor_message == 2) || ((sensor_counter + (-1 * _x_sensor_counter)) == -1)) && ((collision == (_x_sensor_message == 1)) && ((max_delta_counter_init == _x_max_delta_counter_init) && (((_x_sensor_message == 0) || (_x_sensor_message == 1)) || (_x_sensor_message == 2))))))))))))))) && (((((_EL_U_137 == (_x__EL_U_137 || ( !(( !(_x__EL_X_121 || _x__EL_X_122)) || ( !(_x_fault_corruption || _x_fault_deletion)))))) && ((_x_fault_deletion == _EL_X_121) && ((_x_fault_corruption == _EL_X_122) && ((_EL_U_141 == (_x_device_exploded || _x__EL_U_141)) && (_EL_U_144 == (_x__EL_U_144 || ( !((_x_device_exploded || _x__EL_U_141) || ( !_x_collision))))))))) && (_x__J165 == (( !((_J165 && _J175) && _J192)) && (((_J165 && _J175) && _J192) || ((device_exploded || ( !(device_exploded || _EL_U_141))) || _J165))))) && (_x__J175 == (( !((_J165 && _J175) && _J192)) && (((_J165 && _J175) && _J192) || ((( !(( !collision) || (device_exploded || _EL_U_141))) || ( !(_EL_U_144 || ( !(( !collision) || (device_exploded || _EL_U_141)))))) || _J175))))) && (_x__J192 == (( !((_J165 && _J175) && _J192)) && (((_J165 && _J175) && _J192) || ((( !(( !(fault_corruption || fault_deletion)) || ( !(_EL_X_122 || _EL_X_121)))) || ( !(_EL_U_137 || ( !(( !(fault_corruption || fault_deletion)) || ( !(_EL_X_122 || _EL_X_121))))))) || _J192))))));
    sensor_message = _x_sensor_message;
    link_valid_crc = _x_link_valid_crc;
    link_new_data_available = _x_link_new_data_available;
    new_valid_data = _x_new_valid_data;
    _J192 = _x__J192;
    _J175 = _x__J175;
    _J165 = _x__J165;
    _EL_X_121 = _x__EL_X_121;
    _EL_X_122 = _x__EL_X_122;
    fault_deletion = _x_fault_deletion;
    fault_corruption = _x_fault_corruption;
    _EL_U_137 = _x__EL_U_137;
    max_delta_counter_init = _x_max_delta_counter_init;
    _EL_U_141 = _x__EL_U_141;
    device_exploded = _x_device_exploded;
    collision = _x_collision;
    _EL_U_144 = _x__EL_U_144;
    link_out_message = _x_link_out_message;
    sensor_counter = _x_sensor_counter;
    device_last_valid_counter = _x_device_last_valid_counter;
    link_out_counter = _x_link_out_counter;

  }
}
