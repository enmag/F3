extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);
typedef enum {false, true} bool;
bool __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}

int main()
{
float x_1, _x_x_1;
bool _EL_X_97, _x__EL_X_97;
bool _EL_X_102, _x__EL_X_102;
float x_3, _x_x_3;
float x_0, _x_x_0;
float x_2, _x_x_2;
bool _EL_U_100, _x__EL_U_100;

  int __steps_to_fair = __VERIFIER_nondet_int();
  x_1 = __VERIFIER_nondet_float();
  _EL_X_97 = __VERIFIER_nondet_bool();
  _EL_X_102 = __VERIFIER_nondet_bool();
  x_3 = __VERIFIER_nondet_float();
  x_0 = __VERIFIER_nondet_float();
  x_2 = __VERIFIER_nondet_float();
  _EL_U_100 = __VERIFIER_nondet_bool();

  bool __ok = (1 && ( !(_EL_X_102 || _EL_X_97)));
  while (__steps_to_fair >= 0 && __ok) {
    if (((-7.0 <= (x_1 + (-1.0 * x_2))) || ( !((-7.0 <= (x_1 + (-1.0 * x_2))) || _EL_U_100)))) {
      __steps_to_fair = __VERIFIER_nondet_int();
    } else {
      __steps_to_fair--;
    }
    _x_x_1 = __VERIFIER_nondet_float();
    _x__EL_X_97 = __VERIFIER_nondet_bool();
    _x__EL_X_102 = __VERIFIER_nondet_bool();
    _x_x_3 = __VERIFIER_nondet_float();
    _x_x_0 = __VERIFIER_nondet_float();
    _x_x_2 = __VERIFIER_nondet_float();
    _x__EL_U_100 = __VERIFIER_nondet_bool();

    __ok = ((((((((x_2 + (-1.0 * _x_x_0)) <= -15.0) && ((x_3 + (-1.0 * _x_x_0)) <= -2.0)) && (((x_2 + (-1.0 * _x_x_0)) == -15.0) || ((x_3 + (-1.0 * _x_x_0)) == -2.0))) && ((((x_0 + (-1.0 * _x_x_1)) <= -5.0) && ((x_2 + (-1.0 * _x_x_1)) <= -17.0)) && (((x_0 + (-1.0 * _x_x_1)) == -5.0) || ((x_2 + (-1.0 * _x_x_1)) == -17.0)))) && ((((x_1 + (-1.0 * _x_x_2)) <= -17.0) && ((x_3 + (-1.0 * _x_x_2)) <= -14.0)) && (((x_1 + (-1.0 * _x_x_2)) == -17.0) || ((x_3 + (-1.0 * _x_x_2)) == -14.0)))) && ((((x_2 + (-1.0 * _x_x_3)) <= -10.0) && ((x_3 + (-1.0 * _x_x_3)) <= -13.0)) && (((x_2 + (-1.0 * _x_x_3)) == -10.0) || ((x_3 + (-1.0 * _x_x_3)) == -13.0)))) && ((_EL_X_97 == (-3.0 <= (_x_x_1 + (-1.0 * _x_x_3)))) && ((_EL_U_100 == (_x__EL_U_100 || (-7.0 <= (_x_x_1 + (-1.0 * _x_x_2))))) && (_EL_X_102 == ( !(_x__EL_U_100 || (-7.0 <= (_x_x_1 + (-1.0 * _x_x_2)))))))));
    x_1 = _x_x_1;
    _EL_X_97 = _x__EL_X_97;
    _EL_X_102 = _x__EL_X_102;
    x_3 = _x_x_3;
    x_0 = _x_x_0;
    x_2 = _x_x_2;
    _EL_U_100 = _x__EL_U_100;

  }
}
