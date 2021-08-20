extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);
typedef enum {false, true} bool;
bool __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}

int main()
{
float rbc_d, _x_rbc_d;
bool _EL_U_202, _x__EL_U_202;
float _diverge_delta, _x__diverge_delta;
float delta, _x_delta;
bool _EL_U_204, _x__EL_U_204;
float train_v, _x_train_v;
bool _EL_U_206, _x__EL_U_206;
float rbc_m, _x_rbc_m;
float rbc_v_des, _x_rbc_v_des;
float train_a, _x_train_a;
bool _EL_U_208, _x__EL_U_208;
bool rbc_s, _x_rbc_s;
float train_z, _x_train_z;
bool _J250, _x__J250;
float train_c, _x_train_c;
bool _J244, _x__J244;
bool _J238, _x__J238;
bool _J232, _x__J232;

  int __steps_to_fair = __VERIFIER_nondet_int();
  rbc_d = __VERIFIER_nondet_float();
  _EL_U_202 = __VERIFIER_nondet_bool();
  _diverge_delta = __VERIFIER_nondet_float();
  delta = __VERIFIER_nondet_float();
  _EL_U_204 = __VERIFIER_nondet_bool();
  train_v = __VERIFIER_nondet_float();
  _EL_U_206 = __VERIFIER_nondet_bool();
  rbc_m = __VERIFIER_nondet_float();
  rbc_v_des = __VERIFIER_nondet_float();
  train_a = __VERIFIER_nondet_float();
  _EL_U_208 = __VERIFIER_nondet_bool();
  rbc_s = __VERIFIER_nondet_bool();
  train_z = __VERIFIER_nondet_float();
  _J250 = __VERIFIER_nondet_bool();
  train_c = __VERIFIER_nondet_float();
  _J244 = __VERIFIER_nondet_bool();
  _J238 = __VERIFIER_nondet_bool();
  _J232 = __VERIFIER_nondet_bool();

  bool __ok = ((((((((rbc_s && (rbc_v_des == 0.0)) && ((( !(rbc_m <= train_z)) && (train_v == 0.0)) && ((train_a == 0.0) && (train_c == 0.0)))) && (((0.0 <= delta) && (0.0 <= rbc_m)) && ((0.0 <= rbc_d) && (0.0 <= rbc_v_des)))) && (((train_c <= 1.0) && (0.0 <= train_z)) && ((-2.0 <= train_a) && (train_a <= 4.0)))) && ((train_a <= 0.0) || ( !(rbc_v_des <= train_v)))) && (0.0 <= train_v)) && (delta == _diverge_delta)) && ((((( !((_EL_U_208 || ( !((( !(delta <= 0.0)) && ( !(train_v <= 0.0))) || _EL_U_206))) || (_EL_U_204 || ( !((1.0 <= _diverge_delta) || _EL_U_202))))) && ( !_J232)) && ( !_J238)) && ( !_J244)) && ( !_J250)));
  while (__steps_to_fair >= 0 && __ok) {
    if ((((_J232 && _J238) && _J244) && _J250)) {
      __steps_to_fair = __VERIFIER_nondet_int();
    } else {
      __steps_to_fair--;
    }
    _x_rbc_d = __VERIFIER_nondet_float();
    _x__EL_U_202 = __VERIFIER_nondet_bool();
    _x__diverge_delta = __VERIFIER_nondet_float();
    _x_delta = __VERIFIER_nondet_float();
    _x__EL_U_204 = __VERIFIER_nondet_bool();
    _x_train_v = __VERIFIER_nondet_float();
    _x__EL_U_206 = __VERIFIER_nondet_bool();
    _x_rbc_m = __VERIFIER_nondet_float();
    _x_rbc_v_des = __VERIFIER_nondet_float();
    _x_train_a = __VERIFIER_nondet_float();
    _x__EL_U_208 = __VERIFIER_nondet_bool();
    _x_rbc_s = __VERIFIER_nondet_bool();
    _x_train_z = __VERIFIER_nondet_float();
    _x__J250 = __VERIFIER_nondet_bool();
    _x_train_c = __VERIFIER_nondet_float();
    _x__J244 = __VERIFIER_nondet_bool();
    _x__J238 = __VERIFIER_nondet_bool();
    _x__J232 = __VERIFIER_nondet_bool();

    __ok = (((((((((((((((0.0 <= _x_delta) && (0.0 <= _x_rbc_m)) && ((0.0 <= _x_rbc_d) && (0.0 <= _x_rbc_v_des))) && (((_x_train_c <= 1.0) && (0.0 <= _x_train_z)) && ((-2.0 <= _x_train_a) && (_x_train_a <= 4.0)))) && ((_x_train_a <= 0.0) || ( !(_x_rbc_v_des <= _x_train_v)))) && (0.0 <= _x_train_v)) && (( !_x_rbc_s) || ((rbc_m == _x_rbc_m) && (rbc_d == _x_rbc_d)))) && (_x_rbc_s || (((4.0 * rbc_m) + ((-4.0 * _x_rbc_m) + ((rbc_d * rbc_d) + (-1.0 * (_x_rbc_d * _x_rbc_d))))) <= 0.0))) && ((1.0 <= train_c) || ((delta + (train_c + (-1.0 * _x_train_c))) == 0.0))) && (( !(1.0 <= train_c)) || ((_x_train_c == 0.0) && (delta == 0.0)))) && (((2.0 * train_z) + ((-2.0 * _x_train_z) + ((train_a * (delta * delta)) + (2.0 * (delta * train_v))))) == 0.0)) && ((train_v + ((-1.0 * _x_train_v) + (delta * train_a))) == 0.0)) && ((_x_train_a == -2.0) || ( !(((_x_train_c == 0.0) && (train_c == 1.0)) && (rbc_s || (((4.0 * rbc_m) + ((-4.0 * train_z) + ((-4.0 * train_v) + ((-1.0 * (train_v * train_v)) + (rbc_d * rbc_d))))) <= 24.0)))))) && (((delta == _x__diverge_delta) || ( !(1.0 <= _diverge_delta))) && ((1.0 <= _diverge_delta) || ((delta + (_diverge_delta + (-1.0 * _x__diverge_delta))) == 0.0)))) && ((((((_EL_U_204 == (_x__EL_U_204 || ( !(_x__EL_U_202 || (1.0 <= _x__diverge_delta))))) && ((_EL_U_202 == (_x__EL_U_202 || (1.0 <= _x__diverge_delta))) && ((_EL_U_206 == (_x__EL_U_206 || (( !(_x_train_v <= 0.0)) && ( !(_x_delta <= 0.0))))) && (_EL_U_208 == (_x__EL_U_208 || ( !(_x__EL_U_206 || (( !(_x_train_v <= 0.0)) && ( !(_x_delta <= 0.0)))))))))) && (_x__J232 == (( !(((_J232 && _J238) && _J244) && _J250)) && ((((_J232 && _J238) && _J244) && _J250) || (((( !(delta <= 0.0)) && ( !(train_v <= 0.0))) || ( !((( !(delta <= 0.0)) && ( !(train_v <= 0.0))) || _EL_U_206))) || _J232))))) && (_x__J238 == (( !(((_J232 && _J238) && _J244) && _J250)) && ((((_J232 && _J238) && _J244) && _J250) || ((( !((( !(delta <= 0.0)) && ( !(train_v <= 0.0))) || _EL_U_206)) || ( !(_EL_U_208 || ( !((( !(delta <= 0.0)) && ( !(train_v <= 0.0))) || _EL_U_206))))) || _J238))))) && (_x__J244 == (( !(((_J232 && _J238) && _J244) && _J250)) && ((((_J232 && _J238) && _J244) && _J250) || (((1.0 <= _diverge_delta) || ( !((1.0 <= _diverge_delta) || _EL_U_202))) || _J244))))) && (_x__J250 == (( !(((_J232 && _J238) && _J244) && _J250)) && ((((_J232 && _J238) && _J244) && _J250) || ((( !((1.0 <= _diverge_delta) || _EL_U_202)) || ( !(_EL_U_204 || ( !((1.0 <= _diverge_delta) || _EL_U_202))))) || _J250))))));
    rbc_d = _x_rbc_d;
    _EL_U_202 = _x__EL_U_202;
    _diverge_delta = _x__diverge_delta;
    delta = _x_delta;
    _EL_U_204 = _x__EL_U_204;
    train_v = _x_train_v;
    _EL_U_206 = _x__EL_U_206;
    rbc_m = _x_rbc_m;
    rbc_v_des = _x_rbc_v_des;
    train_a = _x_train_a;
    _EL_U_208 = _x__EL_U_208;
    rbc_s = _x_rbc_s;
    train_z = _x_train_z;
    _J250 = _x__J250;
    train_c = _x_train_c;
    _J244 = _x__J244;
    _J238 = _x__J238;
    _J232 = _x__J232;

  }
}
