extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);
typedef enum {false, true} bool;
bool __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}

int main()
{
bool device_exploded, _x_device_exploded;
bool o_collision, _x_o_collision;
int sensor_message, _x_sensor_message;
bool fault_deletion, _x_fault_deletion;
int link_out_message, _x_link_out_message;
bool link_valid_crc, _x_link_valid_crc;
bool link_new_data_available, _x_link_new_data_available;
int link_out_counter, _x_link_out_counter;
bool fault_corruption, _x_fault_corruption;
bool _J133, _x__J133;
bool _J127, _x__J127;
bool _J121, _x__J121;
bool _EL_U_96, _x__EL_U_96;
bool o_valid_explode, _x_o_valid_explode;
int sensor_counter, _x_sensor_counter;
bool _EL_U_98, _x__EL_U_98;
bool _EL_U_101, _x__EL_U_101;

  int __steps_to_fair = __VERIFIER_nondet_int();
  device_exploded = __VERIFIER_nondet_bool();
  o_collision = __VERIFIER_nondet_bool();
  sensor_message = __VERIFIER_nondet_int();
  fault_deletion = __VERIFIER_nondet_bool();
  link_out_message = __VERIFIER_nondet_int();
  link_valid_crc = __VERIFIER_nondet_bool();
  link_new_data_available = __VERIFIER_nondet_bool();
  link_out_counter = __VERIFIER_nondet_int();
  fault_corruption = __VERIFIER_nondet_bool();
  _J133 = __VERIFIER_nondet_bool();
  _J127 = __VERIFIER_nondet_bool();
  _J121 = __VERIFIER_nondet_bool();
  _EL_U_96 = __VERIFIER_nondet_bool();
  o_valid_explode = __VERIFIER_nondet_bool();
  sensor_counter = __VERIFIER_nondet_int();
  _EL_U_98 = __VERIFIER_nondet_bool();
  _EL_U_101 = __VERIFIER_nondet_bool();

  bool __ok = ((((link_new_data_available && link_valid_crc) && (link_out_message == 1)) && ((sensor_message == 2) || ((sensor_message == 0) || (sensor_message == 1)))) && (((( !(( !(( !(o_collision || ( !device_exploded))) || _EL_U_101)) || (_EL_U_98 || ( !(( !(sensor_message == 2)) || _EL_U_96))))) && ( !_J121)) && ( !_J127)) && ( !_J133)));
  while (__steps_to_fair >= 0 && __ok) {
    if (((_J121 && _J127) && _J133)) {
      __steps_to_fair = __VERIFIER_nondet_int();
    } else {
      __steps_to_fair--;
    }
    _x_device_exploded = __VERIFIER_nondet_bool();
    _x_o_collision = __VERIFIER_nondet_bool();
    _x_sensor_message = __VERIFIER_nondet_int();
    _x_fault_deletion = __VERIFIER_nondet_bool();
    _x_link_out_message = __VERIFIER_nondet_int();
    _x_link_valid_crc = __VERIFIER_nondet_bool();
    _x_link_new_data_available = __VERIFIER_nondet_bool();
    _x_link_out_counter = __VERIFIER_nondet_int();
    _x_fault_corruption = __VERIFIER_nondet_bool();
    _x__J133 = __VERIFIER_nondet_bool();
    _x__J127 = __VERIFIER_nondet_bool();
    _x__J121 = __VERIFIER_nondet_bool();
    _x__EL_U_96 = __VERIFIER_nondet_bool();
    _x_o_valid_explode = __VERIFIER_nondet_bool();
    _x_sensor_counter = __VERIFIER_nondet_int();
    _x__EL_U_98 = __VERIFIER_nondet_bool();
    _x__EL_U_101 = __VERIFIER_nondet_bool();

    __ok = (((_x_device_exploded || ( !device_exploded)) && ((_x_o_valid_explode == (o_valid_explode || ((_x_link_new_data_available && _x_link_valid_crc) && (_x_link_out_message == 1)))) && ((( !fault_corruption) || ( !_x_link_valid_crc)) && ((fault_corruption || _x_link_valid_crc) && ((( !fault_deletion) || ( !_x_link_new_data_available)) && ((fault_deletion || (((_x_link_new_data_available == ( !(sensor_message == 2))) && (sensor_message == _x_link_out_message)) && (_x_link_out_counter == sensor_counter))) && ((( !(sensor_message == 2)) || (sensor_counter == _x_sensor_counter)) && (((sensor_message == 2) || ((sensor_counter + (-1 * _x_sensor_counter)) == -1)) && ((((_x_sensor_message == 0) || (_x_sensor_message == 1)) || (_x_sensor_message == 2)) && (o_collision == (o_collision || (_x_sensor_message == 1)))))))))))) && (((((_EL_U_98 == (_x__EL_U_98 || ( !(_x__EL_U_96 || ( !(_x_sensor_message == 2)))))) && ((_EL_U_101 == (_x__EL_U_101 || ( !(_x_o_collision || ( !_x_device_exploded))))) && (_EL_U_96 == (_x__EL_U_96 || ( !(_x_sensor_message == 2)))))) && (_x__J121 == (( !((_J121 && _J127) && _J133)) && (((_J121 && _J127) && _J133) || ((( !(o_collision || ( !device_exploded))) || ( !(( !(o_collision || ( !device_exploded))) || _EL_U_101))) || _J121))))) && (_x__J127 == (( !((_J121 && _J127) && _J133)) && (((_J121 && _J127) && _J133) || ((( !(sensor_message == 2)) || ( !(( !(sensor_message == 2)) || _EL_U_96))) || _J127))))) && (_x__J133 == (( !((_J121 && _J127) && _J133)) && (((_J121 && _J127) && _J133) || ((( !(( !(sensor_message == 2)) || _EL_U_96)) || ( !(_EL_U_98 || ( !(( !(sensor_message == 2)) || _EL_U_96))))) || _J133))))));
    device_exploded = _x_device_exploded;
    o_collision = _x_o_collision;
    sensor_message = _x_sensor_message;
    fault_deletion = _x_fault_deletion;
    link_out_message = _x_link_out_message;
    link_valid_crc = _x_link_valid_crc;
    link_new_data_available = _x_link_new_data_available;
    link_out_counter = _x_link_out_counter;
    fault_corruption = _x_fault_corruption;
    _J133 = _x__J133;
    _J127 = _x__J127;
    _J121 = _x__J121;
    _EL_U_96 = _x__EL_U_96;
    o_valid_explode = _x_o_valid_explode;
    sensor_counter = _x_sensor_counter;
    _EL_U_98 = _x__EL_U_98;
    _EL_U_101 = _x__EL_U_101;

  }
}
