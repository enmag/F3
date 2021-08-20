extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);
typedef enum {false, true} bool;
bool __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}

int main()
{
bool _EL_U_87, _x__EL_U_87;
bool _EL_X_83, _x__EL_X_83;
float x_3, _x_x_3;
float x_2, _x_x_2;
float x_0, _x_x_0;
float x_1, _x_x_1;
bool _EL_X_82, _x__EL_X_82;

  int __steps_to_fair = __VERIFIER_nondet_int();
  _EL_U_87 = __VERIFIER_nondet_bool();
  _EL_X_83 = __VERIFIER_nondet_bool();
  x_3 = __VERIFIER_nondet_float();
  x_2 = __VERIFIER_nondet_float();
  x_0 = __VERIFIER_nondet_float();
  x_1 = __VERIFIER_nondet_float();
  _EL_X_82 = __VERIFIER_nondet_bool();

  bool __ok = (1 && ( !(( !((x_1 + (-1.0 * x_2)) <= 15.0)) || (_EL_X_83 && _EL_U_87))));
  while (__steps_to_fair >= 0 && __ok) {
    if ((( !((x_1 + (-1.0 * x_2)) <= 15.0)) || ( !(( !((x_1 + (-1.0 * x_2)) <= 15.0)) || (_EL_X_83 && _EL_U_87))))) {
      __steps_to_fair = __VERIFIER_nondet_int();
    } else {
      __steps_to_fair--;
    }
    _x__EL_U_87 = __VERIFIER_nondet_bool();
    _x__EL_X_83 = __VERIFIER_nondet_bool();
    _x_x_3 = __VERIFIER_nondet_float();
    _x_x_2 = __VERIFIER_nondet_float();
    _x_x_0 = __VERIFIER_nondet_float();
    _x_x_1 = __VERIFIER_nondet_float();
    _x__EL_X_82 = __VERIFIER_nondet_bool();

    __ok = ((((((((x_1 + (-1.0 * _x_x_0)) <= -9.0) && ((x_2 + (-1.0 * _x_x_0)) <= -6.0)) && (((x_1 + (-1.0 * _x_x_0)) == -9.0) || ((x_2 + (-1.0 * _x_x_0)) == -6.0))) && ((((x_1 + (-1.0 * _x_x_1)) <= -9.0) && ((x_3 + (-1.0 * _x_x_1)) <= -17.0)) && (((x_1 + (-1.0 * _x_x_1)) == -9.0) || ((x_3 + (-1.0 * _x_x_1)) == -17.0)))) && ((((x_0 + (-1.0 * _x_x_2)) <= -14.0) && ((x_3 + (-1.0 * _x_x_2)) <= -6.0)) && (((x_0 + (-1.0 * _x_x_2)) == -14.0) || ((x_3 + (-1.0 * _x_x_2)) == -6.0)))) && ((((x_1 + (-1.0 * _x_x_3)) <= -7.0) && ((x_2 + (-1.0 * _x_x_3)) <= -11.0)) && (((x_1 + (-1.0 * _x_x_3)) == -7.0) || ((x_2 + (-1.0 * _x_x_3)) == -11.0)))) && ((_EL_U_87 == ((_x__EL_U_87 && _x__EL_X_83) || ( !((_x_x_1 + (-1.0 * _x_x_2)) <= 15.0)))) && ((_EL_X_82 == (11.0 <= (_x_x_1 + (-1.0 * _x_x_2)))) && (_EL_X_83 == _x__EL_X_82))));
    _EL_U_87 = _x__EL_U_87;
    _EL_X_83 = _x__EL_X_83;
    x_3 = _x_x_3;
    x_2 = _x_x_2;
    x_0 = _x_x_0;
    x_1 = _x_x_1;
    _EL_X_82 = _x__EL_X_82;

  }
}
