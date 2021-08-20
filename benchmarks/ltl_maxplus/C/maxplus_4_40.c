extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);
typedef enum {false, true} bool;
bool __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}

int main()
{
bool _EL_X_86, _x__EL_X_86;
float x_0, _x_x_0;
bool _EL_X_92, _x__EL_X_92;
float x_2, _x_x_2;
float x_1, _x_x_1;
float x_3, _x_x_3;

  int __steps_to_fair = __VERIFIER_nondet_int();
  _EL_X_86 = __VERIFIER_nondet_bool();
  x_0 = __VERIFIER_nondet_float();
  _EL_X_92 = __VERIFIER_nondet_bool();
  x_2 = __VERIFIER_nondet_float();
  x_1 = __VERIFIER_nondet_float();
  x_3 = __VERIFIER_nondet_float();

  bool __ok = (1 && ( !(( !_EL_X_92) || ( !_EL_X_86))));
  while (__steps_to_fair >= 0 && __ok) {
    if (( !0)) {
      __steps_to_fair = __VERIFIER_nondet_int();
    } else {
      __steps_to_fair--;
    }
    _x__EL_X_86 = __VERIFIER_nondet_bool();
    _x_x_0 = __VERIFIER_nondet_float();
    _x__EL_X_92 = __VERIFIER_nondet_bool();
    _x_x_2 = __VERIFIER_nondet_float();
    _x_x_1 = __VERIFIER_nondet_float();
    _x_x_3 = __VERIFIER_nondet_float();

    __ok = ((((((((x_1 + (-1.0 * _x_x_0)) <= -13.0) && ((x_3 + (-1.0 * _x_x_0)) <= -9.0)) && (((x_1 + (-1.0 * _x_x_0)) == -13.0) || ((x_3 + (-1.0 * _x_x_0)) == -9.0))) && ((((x_1 + (-1.0 * _x_x_1)) <= -1.0) && ((x_2 + (-1.0 * _x_x_1)) <= -1.0)) && (((x_1 + (-1.0 * _x_x_1)) == -1.0) || ((x_2 + (-1.0 * _x_x_1)) == -1.0)))) && ((((x_0 + (-1.0 * _x_x_2)) <= -5.0) && ((x_2 + (-1.0 * _x_x_2)) <= -16.0)) && (((x_0 + (-1.0 * _x_x_2)) == -5.0) || ((x_2 + (-1.0 * _x_x_2)) == -16.0)))) && ((((x_1 + (-1.0 * _x_x_3)) <= -6.0) && ((x_2 + (-1.0 * _x_x_3)) <= -14.0)) && (((x_1 + (-1.0 * _x_x_3)) == -6.0) || ((x_2 + (-1.0 * _x_x_3)) == -14.0)))) && ((_EL_X_92 == ((_x_x_0 + (-1.0 * _x_x_2)) <= 13.0)) && (_EL_X_86 == ((_x_x_0 + (-1.0 * _x_x_3)) <= -18.0))));
    _EL_X_86 = _x__EL_X_86;
    x_0 = _x_x_0;
    _EL_X_92 = _x__EL_X_92;
    x_2 = _x_x_2;
    x_1 = _x_x_1;
    x_3 = _x_x_3;

  }
}
