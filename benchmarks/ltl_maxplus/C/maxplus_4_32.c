extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);
typedef enum {false, true} bool;
bool __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}

int main()
{
bool _EL_X_94, _x__EL_X_94;
bool _EL_U_98, _x__EL_U_98;
float x_3, _x_x_3;
float x_0, _x_x_0;
float x_2, _x_x_2;
float x_1, _x_x_1;

  int __steps_to_fair = __VERIFIER_nondet_int();
  _EL_X_94 = __VERIFIER_nondet_bool();
  _EL_U_98 = __VERIFIER_nondet_bool();
  x_3 = __VERIFIER_nondet_float();
  x_0 = __VERIFIER_nondet_float();
  x_2 = __VERIFIER_nondet_float();
  x_1 = __VERIFIER_nondet_float();

  bool __ok = (1 && ( !((( !((x_0 + (-1.0 * x_3)) <= 5.0)) || _EL_U_98) && ( !_EL_X_94))));
  while (__steps_to_fair >= 0 && __ok) {
    if ((( !((x_0 + (-1.0 * x_3)) <= 5.0)) || ( !(( !((x_0 + (-1.0 * x_3)) <= 5.0)) || _EL_U_98)))) {
      __steps_to_fair = __VERIFIER_nondet_int();
    } else {
      __steps_to_fair--;
    }
    _x__EL_X_94 = __VERIFIER_nondet_bool();
    _x__EL_U_98 = __VERIFIER_nondet_bool();
    _x_x_3 = __VERIFIER_nondet_float();
    _x_x_0 = __VERIFIER_nondet_float();
    _x_x_2 = __VERIFIER_nondet_float();
    _x_x_1 = __VERIFIER_nondet_float();

    __ok = ((((((((x_2 + (-1.0 * _x_x_0)) <= -6.0) && ((x_3 + (-1.0 * _x_x_0)) <= -9.0)) && (((x_2 + (-1.0 * _x_x_0)) == -6.0) || ((x_3 + (-1.0 * _x_x_0)) == -9.0))) && ((((x_1 + (-1.0 * _x_x_1)) <= -12.0) && ((x_2 + (-1.0 * _x_x_1)) <= -7.0)) && (((x_1 + (-1.0 * _x_x_1)) == -12.0) || ((x_2 + (-1.0 * _x_x_1)) == -7.0)))) && ((((x_1 + (-1.0 * _x_x_2)) <= -16.0) && ((x_3 + (-1.0 * _x_x_2)) <= -20.0)) && (((x_1 + (-1.0 * _x_x_2)) == -16.0) || ((x_3 + (-1.0 * _x_x_2)) == -20.0)))) && ((((x_0 + (-1.0 * _x_x_3)) <= -7.0) && ((x_1 + (-1.0 * _x_x_3)) <= -14.0)) && (((x_0 + (-1.0 * _x_x_3)) == -7.0) || ((x_1 + (-1.0 * _x_x_3)) == -14.0)))) && ((_EL_U_98 == (_x__EL_U_98 || ( !((_x_x_0 + (-1.0 * _x_x_3)) <= 5.0)))) && (_EL_X_94 == (20.0 <= (_x_x_1 + (-1.0 * _x_x_2))))));
    _EL_X_94 = _x__EL_X_94;
    _EL_U_98 = _x__EL_U_98;
    x_3 = _x_x_3;
    x_0 = _x_x_0;
    x_2 = _x_x_2;
    x_1 = _x_x_1;

  }
}
