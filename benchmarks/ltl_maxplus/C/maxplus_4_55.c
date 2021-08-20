extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);
typedef enum {false, true} bool;
bool __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}

int main()
{
bool _EL_U_96, _x__EL_U_96;
float x_3, _x_x_3;
float x_0, _x_x_0;
bool _EL_X_94, _x__EL_X_94;
float x_2, _x_x_2;
bool _EL_X_92, _x__EL_X_92;
float x_1, _x_x_1;

  int __steps_to_fair = __VERIFIER_nondet_int();
  _EL_U_96 = __VERIFIER_nondet_bool();
  x_3 = __VERIFIER_nondet_float();
  x_0 = __VERIFIER_nondet_float();
  _EL_X_94 = __VERIFIER_nondet_bool();
  x_2 = __VERIFIER_nondet_float();
  _EL_X_92 = __VERIFIER_nondet_bool();
  x_1 = __VERIFIER_nondet_float();

  bool __ok = (1 && (_EL_X_94 || (((x_0 + (-1.0 * x_3)) <= 17.0) && _EL_U_96)));
  while (__steps_to_fair >= 0 && __ok) {
    if ((_EL_X_94 || ( !(_EL_X_94 || (((x_0 + (-1.0 * x_3)) <= 17.0) && _EL_U_96))))) {
      __steps_to_fair = __VERIFIER_nondet_int();
    } else {
      __steps_to_fair--;
    }
    _x__EL_U_96 = __VERIFIER_nondet_bool();
    _x_x_3 = __VERIFIER_nondet_float();
    _x_x_0 = __VERIFIER_nondet_float();
    _x__EL_X_94 = __VERIFIER_nondet_bool();
    _x_x_2 = __VERIFIER_nondet_float();
    _x__EL_X_92 = __VERIFIER_nondet_bool();
    _x_x_1 = __VERIFIER_nondet_float();

    __ok = ((((((((x_1 + (-1.0 * _x_x_0)) <= -20.0) && ((x_2 + (-1.0 * _x_x_0)) <= -14.0)) && (((x_1 + (-1.0 * _x_x_0)) == -20.0) || ((x_2 + (-1.0 * _x_x_0)) == -14.0))) && ((((x_0 + (-1.0 * _x_x_1)) <= -8.0) && ((x_1 + (-1.0 * _x_x_1)) <= -11.0)) && (((x_0 + (-1.0 * _x_x_1)) == -8.0) || ((x_1 + (-1.0 * _x_x_1)) == -11.0)))) && ((((x_1 + (-1.0 * _x_x_2)) <= -14.0) && ((x_3 + (-1.0 * _x_x_2)) <= -2.0)) && (((x_1 + (-1.0 * _x_x_2)) == -14.0) || ((x_3 + (-1.0 * _x_x_2)) == -2.0)))) && ((((x_1 + (-1.0 * _x_x_3)) <= -2.0) && ((x_2 + (-1.0 * _x_x_3)) <= -9.0)) && (((x_1 + (-1.0 * _x_x_3)) == -2.0) || ((x_2 + (-1.0 * _x_x_3)) == -9.0)))) && ((_EL_U_96 == (_x__EL_X_94 || (_x__EL_U_96 && ((_x_x_0 + (-1.0 * _x_x_3)) <= 17.0)))) && ((_EL_X_92 == (16.0 <= (_x_x_1 + (-1.0 * _x_x_3)))) && (_EL_X_94 == _x__EL_X_92))));
    _EL_U_96 = _x__EL_U_96;
    x_3 = _x_x_3;
    x_0 = _x_x_0;
    _EL_X_94 = _x__EL_X_94;
    x_2 = _x_x_2;
    _EL_X_92 = _x__EL_X_92;
    x_1 = _x_x_1;

  }
}
