extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);
typedef enum {false, true} bool;
bool __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}

int main()
{
float x_2, _x_x_2;
bool _EL_X_92, _x__EL_X_92;
bool _EL_U_99, _x__EL_U_99;
float x_3, _x_x_3;
float x_1, _x_x_1;
float x_0, _x_x_0;
bool _EL_X_90, _x__EL_X_90;

  int __steps_to_fair = __VERIFIER_nondet_int();
  x_2 = __VERIFIER_nondet_float();
  _EL_X_92 = __VERIFIER_nondet_bool();
  _EL_U_99 = __VERIFIER_nondet_bool();
  x_3 = __VERIFIER_nondet_float();
  x_1 = __VERIFIER_nondet_float();
  x_0 = __VERIFIER_nondet_float();
  _EL_X_90 = __VERIFIER_nondet_bool();

  bool __ok = (1 && ( !(( !(-15.0 <= (x_0 + (-1.0 * x_1)))) || (_EL_U_99 && ( !_EL_X_92)))));
  while (__steps_to_fair >= 0 && __ok) {
    if ((( !(-15.0 <= (x_0 + (-1.0 * x_1)))) || ( !(( !(-15.0 <= (x_0 + (-1.0 * x_1)))) || (_EL_U_99 && ( !_EL_X_92)))))) {
      __steps_to_fair = __VERIFIER_nondet_int();
    } else {
      __steps_to_fair--;
    }
    _x_x_2 = __VERIFIER_nondet_float();
    _x__EL_X_92 = __VERIFIER_nondet_bool();
    _x__EL_U_99 = __VERIFIER_nondet_bool();
    _x_x_3 = __VERIFIER_nondet_float();
    _x_x_1 = __VERIFIER_nondet_float();
    _x_x_0 = __VERIFIER_nondet_float();
    _x__EL_X_90 = __VERIFIER_nondet_bool();

    __ok = ((((((((x_1 + (-1.0 * _x_x_0)) <= -14.0) && ((x_2 + (-1.0 * _x_x_0)) <= -17.0)) && (((x_1 + (-1.0 * _x_x_0)) == -14.0) || ((x_2 + (-1.0 * _x_x_0)) == -17.0))) && ((((x_0 + (-1.0 * _x_x_1)) <= -8.0) && ((x_1 + (-1.0 * _x_x_1)) <= -17.0)) && (((x_0 + (-1.0 * _x_x_1)) == -8.0) || ((x_1 + (-1.0 * _x_x_1)) == -17.0)))) && ((((x_0 + (-1.0 * _x_x_2)) <= -11.0) && ((x_3 + (-1.0 * _x_x_2)) <= -15.0)) && (((x_0 + (-1.0 * _x_x_2)) == -11.0) || ((x_3 + (-1.0 * _x_x_2)) == -15.0)))) && ((((x_0 + (-1.0 * _x_x_3)) <= -18.0) && ((x_1 + (-1.0 * _x_x_3)) <= -4.0)) && (((x_0 + (-1.0 * _x_x_3)) == -18.0) || ((x_1 + (-1.0 * _x_x_3)) == -4.0)))) && ((_EL_U_99 == ((_x__EL_U_99 && ( !_x__EL_X_92)) || ( !(-15.0 <= (_x_x_0 + (-1.0 * _x_x_1)))))) && ((_EL_X_90 == (16.0 <= (_x_x_0 + (-1.0 * _x_x_2)))) && (_EL_X_92 == _x__EL_X_90))));
    x_2 = _x_x_2;
    _EL_X_92 = _x__EL_X_92;
    _EL_U_99 = _x__EL_U_99;
    x_3 = _x_x_3;
    x_1 = _x_x_1;
    x_0 = _x_x_0;
    _EL_X_90 = _x__EL_X_90;

  }
}
