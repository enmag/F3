extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);
typedef enum {false, true} bool;
bool __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}

int main()
{
float x_0, _x_x_0;
bool _J127, _x__J127;
bool _J122, _x__J122;
bool _EL_U_96, _x__EL_U_96;
bool _EL_X_87, _x__EL_X_87;
float x_3, _x_x_3;
float x_2, _x_x_2;
float x_1, _x_x_1;
bool _EL_U_100, _x__EL_U_100;

  int __steps_to_fair = __VERIFIER_nondet_int();
  x_0 = __VERIFIER_nondet_float();
  _J127 = __VERIFIER_nondet_bool();
  _J122 = __VERIFIER_nondet_bool();
  _EL_U_96 = __VERIFIER_nondet_bool();
  _EL_X_87 = __VERIFIER_nondet_bool();
  x_3 = __VERIFIER_nondet_float();
  x_2 = __VERIFIER_nondet_float();
  x_1 = __VERIFIER_nondet_float();
  _EL_U_100 = __VERIFIER_nondet_bool();

  bool __ok = (1 && (((_EL_U_100 || (( !((x_1 + (-1.0 * x_3)) <= 11.0)) || (_EL_X_87 && _EL_U_96))) && ( !_J122)) && ( !_J127)));
  while (__steps_to_fair >= 0 && __ok) {
    if ((_J122 && _J127)) {
      __steps_to_fair = __VERIFIER_nondet_int();
    } else {
      __steps_to_fair--;
    }
    _x_x_0 = __VERIFIER_nondet_float();
    _x__J127 = __VERIFIER_nondet_bool();
    _x__J122 = __VERIFIER_nondet_bool();
    _x__EL_U_96 = __VERIFIER_nondet_bool();
    _x__EL_X_87 = __VERIFIER_nondet_bool();
    _x_x_3 = __VERIFIER_nondet_float();
    _x_x_2 = __VERIFIER_nondet_float();
    _x_x_1 = __VERIFIER_nondet_float();
    _x__EL_U_100 = __VERIFIER_nondet_bool();

    __ok = ((((((((x_1 + (-1.0 * _x_x_0)) <= -2.0) && ((x_2 + (-1.0 * _x_x_0)) <= -13.0)) && (((x_1 + (-1.0 * _x_x_0)) == -2.0) || ((x_2 + (-1.0 * _x_x_0)) == -13.0))) && ((((x_2 + (-1.0 * _x_x_1)) <= -6.0) && ((x_3 + (-1.0 * _x_x_1)) <= -7.0)) && (((x_2 + (-1.0 * _x_x_1)) == -6.0) || ((x_3 + (-1.0 * _x_x_1)) == -7.0)))) && ((((x_0 + (-1.0 * _x_x_2)) <= -6.0) && ((x_2 + (-1.0 * _x_x_2)) <= -1.0)) && (((x_0 + (-1.0 * _x_x_2)) == -6.0) || ((x_2 + (-1.0 * _x_x_2)) == -1.0)))) && ((((x_0 + (-1.0 * _x_x_3)) <= -18.0) && ((x_3 + (-1.0 * _x_x_3)) <= -3.0)) && (((x_0 + (-1.0 * _x_x_3)) == -18.0) || ((x_3 + (-1.0 * _x_x_3)) == -3.0)))) && ((((_EL_U_100 == (_x__EL_U_100 || ((_x__EL_U_96 && _x__EL_X_87) || ( !((_x_x_1 + (-1.0 * _x_x_3)) <= 11.0))))) && ((_EL_X_87 == (-13.0 <= (_x_x_0 + (-1.0 * _x_x_3)))) && (_EL_U_96 == ((_x__EL_U_96 && _x__EL_X_87) || ( !((_x_x_1 + (-1.0 * _x_x_3)) <= 11.0)))))) && (_x__J122 == (( !(_J122 && _J127)) && ((_J122 && _J127) || ((( !((x_1 + (-1.0 * x_3)) <= 11.0)) || ( !(( !((x_1 + (-1.0 * x_3)) <= 11.0)) || (_EL_X_87 && _EL_U_96)))) || _J122))))) && (_x__J127 == (( !(_J122 && _J127)) && ((_J122 && _J127) || (((( !((x_1 + (-1.0 * x_3)) <= 11.0)) || (_EL_X_87 && _EL_U_96)) || ( !(_EL_U_100 || (( !((x_1 + (-1.0 * x_3)) <= 11.0)) || (_EL_X_87 && _EL_U_96))))) || _J127))))));
    x_0 = _x_x_0;
    _J127 = _x__J127;
    _J122 = _x__J122;
    _EL_U_96 = _x__EL_U_96;
    _EL_X_87 = _x__EL_X_87;
    x_3 = _x_x_3;
    x_2 = _x_x_2;
    x_1 = _x_x_1;
    _EL_U_100 = _x__EL_U_100;

  }
}
