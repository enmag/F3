extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);
typedef enum {false, true} bool;
bool __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}

int main()
{
float x_2, _x_x_2;
float x_1, _x_x_1;
bool _J124, _x__J124;
bool _J119, _x__J119;
bool _EL_U_92, _x__EL_U_92;
float x_3, _x_x_3;
float x_0, _x_x_0;
bool _EL_X_90, _x__EL_X_90;
bool _EL_U_96, _x__EL_U_96;

  int __steps_to_fair = __VERIFIER_nondet_int();
  x_2 = __VERIFIER_nondet_float();
  x_1 = __VERIFIER_nondet_float();
  _J124 = __VERIFIER_nondet_bool();
  _J119 = __VERIFIER_nondet_bool();
  _EL_U_92 = __VERIFIER_nondet_bool();
  x_3 = __VERIFIER_nondet_float();
  x_0 = __VERIFIER_nondet_float();
  _EL_X_90 = __VERIFIER_nondet_bool();
  _EL_U_96 = __VERIFIER_nondet_bool();

  bool __ok = (1 && (((_EL_U_96 || (( !_EL_X_90) || (((x_0 + (-1.0 * x_3)) <= 5.0) && _EL_U_92))) && ( !_J119)) && ( !_J124)));
  while (__steps_to_fair >= 0 && __ok) {
    if ((_J119 && _J124)) {
      __steps_to_fair = __VERIFIER_nondet_int();
    } else {
      __steps_to_fair--;
    }
    _x_x_2 = __VERIFIER_nondet_float();
    _x_x_1 = __VERIFIER_nondet_float();
    _x__J124 = __VERIFIER_nondet_bool();
    _x__J119 = __VERIFIER_nondet_bool();
    _x__EL_U_92 = __VERIFIER_nondet_bool();
    _x_x_3 = __VERIFIER_nondet_float();
    _x_x_0 = __VERIFIER_nondet_float();
    _x__EL_X_90 = __VERIFIER_nondet_bool();
    _x__EL_U_96 = __VERIFIER_nondet_bool();

    __ok = ((((((((x_2 + (-1.0 * _x_x_0)) <= -9.0) && ((x_3 + (-1.0 * _x_x_0)) <= -4.0)) && (((x_2 + (-1.0 * _x_x_0)) == -9.0) || ((x_3 + (-1.0 * _x_x_0)) == -4.0))) && ((((x_2 + (-1.0 * _x_x_1)) <= -2.0) && ((x_3 + (-1.0 * _x_x_1)) <= -15.0)) && (((x_2 + (-1.0 * _x_x_1)) == -2.0) || ((x_3 + (-1.0 * _x_x_1)) == -15.0)))) && ((((x_0 + (-1.0 * _x_x_2)) <= -6.0) && ((x_1 + (-1.0 * _x_x_2)) <= -11.0)) && (((x_0 + (-1.0 * _x_x_2)) == -6.0) || ((x_1 + (-1.0 * _x_x_2)) == -11.0)))) && ((((x_1 + (-1.0 * _x_x_3)) <= -7.0) && ((x_3 + (-1.0 * _x_x_3)) <= -4.0)) && (((x_1 + (-1.0 * _x_x_3)) == -7.0) || ((x_3 + (-1.0 * _x_x_3)) == -4.0)))) && ((((_EL_U_96 == (_x__EL_U_96 || ((_x__EL_U_92 && ((_x_x_0 + (-1.0 * _x_x_3)) <= 5.0)) || ( !_x__EL_X_90)))) && ((_EL_X_90 == ((_x_x_1 + (-1.0 * _x_x_3)) <= -7.0)) && (_EL_U_92 == ((_x__EL_U_92 && ((_x_x_0 + (-1.0 * _x_x_3)) <= 5.0)) || ( !_x__EL_X_90))))) && (_x__J119 == (( !(_J119 && _J124)) && ((_J119 && _J124) || ((( !_EL_X_90) || ( !(( !_EL_X_90) || (((x_0 + (-1.0 * x_3)) <= 5.0) && _EL_U_92)))) || _J119))))) && (_x__J124 == (( !(_J119 && _J124)) && ((_J119 && _J124) || (((( !_EL_X_90) || (((x_0 + (-1.0 * x_3)) <= 5.0) && _EL_U_92)) || ( !(_EL_U_96 || (( !_EL_X_90) || (((x_0 + (-1.0 * x_3)) <= 5.0) && _EL_U_92))))) || _J124))))));
    x_2 = _x_x_2;
    x_1 = _x_x_1;
    _J124 = _x__J124;
    _J119 = _x__J119;
    _EL_U_92 = _x__EL_U_92;
    x_3 = _x_x_3;
    x_0 = _x_x_0;
    _EL_X_90 = _x__EL_X_90;
    _EL_U_96 = _x__EL_U_96;

  }
}
