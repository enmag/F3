extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);
typedef enum {false, true} bool;
bool __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}

int main()
{
bool _EL_X_98, _x__EL_X_98;
float x_0, _x_x_0;
float x_2, _x_x_2;
float x_1, _x_x_1;
float x_3, _x_x_3;
bool _EL_U_97, _x__EL_U_97;

  int __steps_to_fair = __VERIFIER_nondet_int();
  _EL_X_98 = __VERIFIER_nondet_bool();
  x_0 = __VERIFIER_nondet_float();
  x_2 = __VERIFIER_nondet_float();
  x_1 = __VERIFIER_nondet_float();
  x_3 = __VERIFIER_nondet_float();
  _EL_U_97 = __VERIFIER_nondet_bool();

  bool __ok = (1 && ( !(((x_1 + (-1.0 * x_2)) <= -1.0) || _EL_X_98)));
  while (__steps_to_fair >= 0 && __ok) {
    if ((((x_1 + (-1.0 * x_2)) <= -9.0) || ( !(((x_1 + (-1.0 * x_2)) <= -9.0) || _EL_U_97)))) {
      __steps_to_fair = __VERIFIER_nondet_int();
    } else {
      __steps_to_fair--;
    }
    _x__EL_X_98 = __VERIFIER_nondet_bool();
    _x_x_0 = __VERIFIER_nondet_float();
    _x_x_2 = __VERIFIER_nondet_float();
    _x_x_1 = __VERIFIER_nondet_float();
    _x_x_3 = __VERIFIER_nondet_float();
    _x__EL_U_97 = __VERIFIER_nondet_bool();

    __ok = ((((((((x_1 + (-1.0 * _x_x_0)) <= -6.0) && ((x_3 + (-1.0 * _x_x_0)) <= -17.0)) && (((x_1 + (-1.0 * _x_x_0)) == -6.0) || ((x_3 + (-1.0 * _x_x_0)) == -17.0))) && ((((x_0 + (-1.0 * _x_x_1)) <= -2.0) && ((x_3 + (-1.0 * _x_x_1)) <= -20.0)) && (((x_0 + (-1.0 * _x_x_1)) == -2.0) || ((x_3 + (-1.0 * _x_x_1)) == -20.0)))) && ((((x_0 + (-1.0 * _x_x_2)) <= -8.0) && ((x_1 + (-1.0 * _x_x_2)) <= -14.0)) && (((x_0 + (-1.0 * _x_x_2)) == -8.0) || ((x_1 + (-1.0 * _x_x_2)) == -14.0)))) && ((((x_1 + (-1.0 * _x_x_3)) <= -18.0) && ((x_2 + (-1.0 * _x_x_3)) <= -16.0)) && (((x_1 + (-1.0 * _x_x_3)) == -18.0) || ((x_2 + (-1.0 * _x_x_3)) == -16.0)))) && ((_EL_U_97 == (_x__EL_U_97 || ((_x_x_1 + (-1.0 * _x_x_2)) <= -9.0))) && (_EL_X_98 == (_x__EL_U_97 || ((_x_x_1 + (-1.0 * _x_x_2)) <= -9.0)))));
    _EL_X_98 = _x__EL_X_98;
    x_0 = _x_x_0;
    x_2 = _x_x_2;
    x_1 = _x_x_1;
    x_3 = _x_x_3;
    _EL_U_97 = _x__EL_U_97;

  }
}
