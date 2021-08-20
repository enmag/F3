extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);
typedef enum {false, true} bool;
bool __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}

int main()
{
float x_3, _x_x_3;
bool _J128, _x__J128;
bool _J117, _x__J117;
bool _EL_X_102, _x__EL_X_102;
bool _EL_U_99, _x__EL_U_99;
float x_2, _x_x_2;
float x_0, _x_x_0;
float x_1, _x_x_1;
bool _EL_U_101, _x__EL_U_101;

  int __steps_to_fair = __VERIFIER_nondet_int();
  x_3 = __VERIFIER_nondet_float();
  _J128 = __VERIFIER_nondet_bool();
  _J117 = __VERIFIER_nondet_bool();
  _EL_X_102 = __VERIFIER_nondet_bool();
  _EL_U_99 = __VERIFIER_nondet_bool();
  x_2 = __VERIFIER_nondet_float();
  x_0 = __VERIFIER_nondet_float();
  x_1 = __VERIFIER_nondet_float();
  _EL_U_101 = __VERIFIER_nondet_bool();

  bool __ok = (1 && ((_EL_X_102 && ( !_J117)) && ( !_J128)));
  while (__steps_to_fair >= 0 && __ok) {
    if ((_J117 && _J128)) {
      __steps_to_fair = __VERIFIER_nondet_int();
    } else {
      __steps_to_fair--;
    }
    _x_x_3 = __VERIFIER_nondet_float();
    _x__J128 = __VERIFIER_nondet_bool();
    _x__J117 = __VERIFIER_nondet_bool();
    _x__EL_X_102 = __VERIFIER_nondet_bool();
    _x__EL_U_99 = __VERIFIER_nondet_bool();
    _x_x_2 = __VERIFIER_nondet_float();
    _x_x_0 = __VERIFIER_nondet_float();
    _x_x_1 = __VERIFIER_nondet_float();
    _x__EL_U_101 = __VERIFIER_nondet_bool();

    __ok = ((((((((x_0 + (-1.0 * _x_x_0)) <= -10.0) && ((x_2 + (-1.0 * _x_x_0)) <= -7.0)) && (((x_0 + (-1.0 * _x_x_0)) == -10.0) || ((x_2 + (-1.0 * _x_x_0)) == -7.0))) && ((((x_0 + (-1.0 * _x_x_1)) <= -8.0) && ((x_3 + (-1.0 * _x_x_1)) <= -3.0)) && (((x_0 + (-1.0 * _x_x_1)) == -8.0) || ((x_3 + (-1.0 * _x_x_1)) == -3.0)))) && ((((x_1 + (-1.0 * _x_x_2)) <= -3.0) && ((x_3 + (-1.0 * _x_x_2)) <= -5.0)) && (((x_1 + (-1.0 * _x_x_2)) == -3.0) || ((x_3 + (-1.0 * _x_x_2)) == -5.0)))) && ((((x_1 + (-1.0 * _x_x_3)) <= -6.0) && ((x_2 + (-1.0 * _x_x_3)) <= -12.0)) && (((x_1 + (-1.0 * _x_x_3)) == -6.0) || ((x_2 + (-1.0 * _x_x_3)) == -12.0)))) && ((((_EL_X_102 == ((_x__EL_U_101 && ( !(_x__EL_U_99 || ( !((_x_x_0 + (-1.0 * _x_x_3)) <= -10.0))))) || ( !((_x_x_2 + (-1.0 * _x_x_3)) <= 11.0)))) && ((_EL_U_99 == (_x__EL_U_99 || ( !((_x_x_0 + (-1.0 * _x_x_3)) <= -10.0)))) && (_EL_U_101 == ((_x__EL_U_101 && ( !(_x__EL_U_99 || ( !((_x_x_0 + (-1.0 * _x_x_3)) <= -10.0))))) || ( !((_x_x_2 + (-1.0 * _x_x_3)) <= 11.0)))))) && (_x__J117 == (( !(_J117 && _J128)) && ((_J117 && _J128) || ((( !((x_0 + (-1.0 * x_3)) <= -10.0)) || ( !(( !((x_0 + (-1.0 * x_3)) <= -10.0)) || _EL_U_99))) || _J117))))) && (_x__J128 == (( !(_J117 && _J128)) && ((_J117 && _J128) || ((( !((x_2 + (-1.0 * x_3)) <= 11.0)) || ( !(( !((x_2 + (-1.0 * x_3)) <= 11.0)) || (_EL_U_101 && ( !(( !((x_0 + (-1.0 * x_3)) <= -10.0)) || _EL_U_99)))))) || _J128))))));
    x_3 = _x_x_3;
    _J128 = _x__J128;
    _J117 = _x__J117;
    _EL_X_102 = _x__EL_X_102;
    _EL_U_99 = _x__EL_U_99;
    x_2 = _x_x_2;
    x_0 = _x_x_0;
    x_1 = _x_x_1;
    _EL_U_101 = _x__EL_U_101;

  }
}
