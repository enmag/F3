extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);
typedef enum {false, true} bool;
bool __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}

int main()
{
float x_1, _x_x_1;
bool _EL_X_94, _x__EL_X_94;
bool _EL_X_96, _x__EL_X_96;
bool _EL_X_91, _x__EL_X_91;
float x_3, _x_x_3;
float x_2, _x_x_2;
float x_0, _x_x_0;

  int __steps_to_fair = __VERIFIER_nondet_int();
  x_1 = __VERIFIER_nondet_float();
  _EL_X_94 = __VERIFIER_nondet_bool();
  _EL_X_96 = __VERIFIER_nondet_bool();
  _EL_X_91 = __VERIFIER_nondet_bool();
  x_3 = __VERIFIER_nondet_float();
  x_2 = __VERIFIER_nondet_float();
  x_0 = __VERIFIER_nondet_float();

  bool __ok = (1 && ( !(( !_EL_X_96) || ( !_EL_X_94))));
  while (__steps_to_fair >= 0 && __ok) {
    if (( !0)) {
      __steps_to_fair = __VERIFIER_nondet_int();
    } else {
      __steps_to_fair--;
    }
    _x_x_1 = __VERIFIER_nondet_float();
    _x__EL_X_94 = __VERIFIER_nondet_bool();
    _x__EL_X_96 = __VERIFIER_nondet_bool();
    _x__EL_X_91 = __VERIFIER_nondet_bool();
    _x_x_3 = __VERIFIER_nondet_float();
    _x_x_2 = __VERIFIER_nondet_float();
    _x_x_0 = __VERIFIER_nondet_float();

    __ok = ((((((((x_1 + (-1.0 * _x_x_0)) <= -8.0) && ((x_2 + (-1.0 * _x_x_0)) <= -14.0)) && (((x_1 + (-1.0 * _x_x_0)) == -8.0) || ((x_2 + (-1.0 * _x_x_0)) == -14.0))) && ((((x_0 + (-1.0 * _x_x_1)) <= -8.0) && ((x_3 + (-1.0 * _x_x_1)) <= -9.0)) && (((x_0 + (-1.0 * _x_x_1)) == -8.0) || ((x_3 + (-1.0 * _x_x_1)) == -9.0)))) && ((((x_1 + (-1.0 * _x_x_2)) <= -20.0) && ((x_2 + (-1.0 * _x_x_2)) <= -13.0)) && (((x_1 + (-1.0 * _x_x_2)) == -20.0) || ((x_2 + (-1.0 * _x_x_2)) == -13.0)))) && ((((x_0 + (-1.0 * _x_x_3)) <= -20.0) && ((x_2 + (-1.0 * _x_x_3)) <= -11.0)) && (((x_0 + (-1.0 * _x_x_3)) == -20.0) || ((x_2 + (-1.0 * _x_x_3)) == -11.0)))) && ((_EL_X_94 == _x__EL_X_91) && ((_EL_X_96 == ((_x_x_0 + (-1.0 * _x_x_3)) <= -3.0)) && (_EL_X_91 == (-13.0 <= (_x_x_0 + (-1.0 * _x_x_2)))))));
    x_1 = _x_x_1;
    _EL_X_94 = _x__EL_X_94;
    _EL_X_96 = _x__EL_X_96;
    _EL_X_91 = _x__EL_X_91;
    x_3 = _x_x_3;
    x_2 = _x_x_2;
    x_0 = _x_x_0;

  }
}
