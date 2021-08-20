extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);
typedef enum {false, true} bool;
bool __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}

int main()
{
bool _EL_X_95, _x__EL_X_95;
float x_1, _x_x_1;
float x_0, _x_x_0;
bool _EL_U_101, _x__EL_U_101;
float x_3, _x_x_3;
float x_2, _x_x_2;

  int __steps_to_fair = __VERIFIER_nondet_int();
  _EL_X_95 = __VERIFIER_nondet_bool();
  x_1 = __VERIFIER_nondet_float();
  x_0 = __VERIFIER_nondet_float();
  _EL_U_101 = __VERIFIER_nondet_bool();
  x_3 = __VERIFIER_nondet_float();
  x_2 = __VERIFIER_nondet_float();

  bool __ok = (1 && (_EL_U_101 || ( !(((x_0 + (-1.0 * x_1)) <= 4.0) || ( !_EL_X_95)))));
  while (__steps_to_fair >= 0 && __ok) {
    if ((( !(((x_0 + (-1.0 * x_1)) <= 4.0) || ( !_EL_X_95))) || ( !(_EL_U_101 || ( !(((x_0 + (-1.0 * x_1)) <= 4.0) || ( !_EL_X_95))))))) {
      __steps_to_fair = __VERIFIER_nondet_int();
    } else {
      __steps_to_fair--;
    }
    _x__EL_X_95 = __VERIFIER_nondet_bool();
    _x_x_1 = __VERIFIER_nondet_float();
    _x_x_0 = __VERIFIER_nondet_float();
    _x__EL_U_101 = __VERIFIER_nondet_bool();
    _x_x_3 = __VERIFIER_nondet_float();
    _x_x_2 = __VERIFIER_nondet_float();

    __ok = ((((((((x_0 + (-1.0 * _x_x_0)) <= -5.0) && ((x_2 + (-1.0 * _x_x_0)) <= -10.0)) && (((x_0 + (-1.0 * _x_x_0)) == -5.0) || ((x_2 + (-1.0 * _x_x_0)) == -10.0))) && ((((x_2 + (-1.0 * _x_x_1)) <= -18.0) && ((x_3 + (-1.0 * _x_x_1)) <= -14.0)) && (((x_2 + (-1.0 * _x_x_1)) == -18.0) || ((x_3 + (-1.0 * _x_x_1)) == -14.0)))) && ((((x_1 + (-1.0 * _x_x_2)) <= -17.0) && ((x_3 + (-1.0 * _x_x_2)) <= -13.0)) && (((x_1 + (-1.0 * _x_x_2)) == -17.0) || ((x_3 + (-1.0 * _x_x_2)) == -13.0)))) && ((((x_0 + (-1.0 * _x_x_3)) <= -20.0) && ((x_3 + (-1.0 * _x_x_3)) <= -14.0)) && (((x_0 + (-1.0 * _x_x_3)) == -20.0) || ((x_3 + (-1.0 * _x_x_3)) == -14.0)))) && ((_EL_X_95 == (9.0 <= (_x_x_0 + (-1.0 * _x_x_3)))) && (_EL_U_101 == (_x__EL_U_101 || ( !(( !_x__EL_X_95) || ((_x_x_0 + (-1.0 * _x_x_1)) <= 4.0)))))));
    _EL_X_95 = _x__EL_X_95;
    x_1 = _x_x_1;
    x_0 = _x_x_0;
    _EL_U_101 = _x__EL_U_101;
    x_3 = _x_x_3;
    x_2 = _x_x_2;

  }
}
