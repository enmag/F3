extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);
typedef enum {false, true} bool;
bool __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}

int main()
{
float x_1, _x_x_1;
bool _EL_X_90, _x__EL_X_90;
float x_3, _x_x_3;
float x_2, _x_x_2;
bool _EL_U_89, _x__EL_U_89;
float x_0, _x_x_0;

  int __steps_to_fair = __VERIFIER_nondet_int();
  x_1 = __VERIFIER_nondet_float();
  _EL_X_90 = __VERIFIER_nondet_bool();
  x_3 = __VERIFIER_nondet_float();
  x_2 = __VERIFIER_nondet_float();
  _EL_U_89 = __VERIFIER_nondet_bool();
  x_0 = __VERIFIER_nondet_float();

  bool __ok = (1 && ( !(((x_2 + (-1.0 * x_3)) <= -14.0) || _EL_X_90)));
  while (__steps_to_fair >= 0 && __ok) {
    if ((((x_1 + (-1.0 * x_2)) <= 1.0) || ( !(((x_1 + (-1.0 * x_2)) <= 1.0) || _EL_U_89)))) {
      __steps_to_fair = __VERIFIER_nondet_int();
    } else {
      __steps_to_fair--;
    }
    _x_x_1 = __VERIFIER_nondet_float();
    _x__EL_X_90 = __VERIFIER_nondet_bool();
    _x_x_3 = __VERIFIER_nondet_float();
    _x_x_2 = __VERIFIER_nondet_float();
    _x__EL_U_89 = __VERIFIER_nondet_bool();
    _x_x_0 = __VERIFIER_nondet_float();

    __ok = ((((((((x_2 + (-1.0 * _x_x_0)) <= -8.0) && ((x_3 + (-1.0 * _x_x_0)) <= -1.0)) && (((x_2 + (-1.0 * _x_x_0)) == -8.0) || ((x_3 + (-1.0 * _x_x_0)) == -1.0))) && ((((x_1 + (-1.0 * _x_x_1)) <= -14.0) && ((x_3 + (-1.0 * _x_x_1)) <= -1.0)) && (((x_1 + (-1.0 * _x_x_1)) == -14.0) || ((x_3 + (-1.0 * _x_x_1)) == -1.0)))) && ((((x_0 + (-1.0 * _x_x_2)) <= -1.0) && ((x_1 + (-1.0 * _x_x_2)) <= -4.0)) && (((x_0 + (-1.0 * _x_x_2)) == -1.0) || ((x_1 + (-1.0 * _x_x_2)) == -4.0)))) && ((((x_0 + (-1.0 * _x_x_3)) <= -2.0) && ((x_2 + (-1.0 * _x_x_3)) <= -1.0)) && (((x_0 + (-1.0 * _x_x_3)) == -2.0) || ((x_2 + (-1.0 * _x_x_3)) == -1.0)))) && ((_EL_U_89 == (_x__EL_U_89 || ((_x_x_1 + (-1.0 * _x_x_2)) <= 1.0))) && (_EL_X_90 == (_x__EL_U_89 || ((_x_x_1 + (-1.0 * _x_x_2)) <= 1.0)))));
    x_1 = _x_x_1;
    _EL_X_90 = _x__EL_X_90;
    x_3 = _x_x_3;
    x_2 = _x_x_2;
    _EL_U_89 = _x__EL_U_89;
    x_0 = _x_x_0;

  }
}
