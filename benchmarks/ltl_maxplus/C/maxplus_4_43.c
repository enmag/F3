extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);
typedef enum {false, true} bool;
bool __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}

int main()
{
bool _EL_X_85, _x__EL_X_85;
bool _EL_U_94, _x__EL_U_94;
float x_2, _x_x_2;
float x_0, _x_x_0;
float x_3, _x_x_3;
float x_1, _x_x_1;

  int __steps_to_fair = __VERIFIER_nondet_int();
  _EL_X_85 = __VERIFIER_nondet_bool();
  _EL_U_94 = __VERIFIER_nondet_bool();
  x_2 = __VERIFIER_nondet_float();
  x_0 = __VERIFIER_nondet_float();
  x_3 = __VERIFIER_nondet_float();
  x_1 = __VERIFIER_nondet_float();

  bool __ok = (1 && ( !(( !(( !(2.0 <= (x_0 + (-1.0 * x_2)))) || _EL_U_94)) && ( !_EL_X_85))));
  while (__steps_to_fair >= 0 && __ok) {
    if ((( !(2.0 <= (x_0 + (-1.0 * x_2)))) || ( !(( !(2.0 <= (x_0 + (-1.0 * x_2)))) || _EL_U_94)))) {
      __steps_to_fair = __VERIFIER_nondet_int();
    } else {
      __steps_to_fair--;
    }
    _x__EL_X_85 = __VERIFIER_nondet_bool();
    _x__EL_U_94 = __VERIFIER_nondet_bool();
    _x_x_2 = __VERIFIER_nondet_float();
    _x_x_0 = __VERIFIER_nondet_float();
    _x_x_3 = __VERIFIER_nondet_float();
    _x_x_1 = __VERIFIER_nondet_float();

    __ok = ((((((((x_1 + (-1.0 * _x_x_0)) <= -11.0) && ((x_3 + (-1.0 * _x_x_0)) <= -10.0)) && (((x_1 + (-1.0 * _x_x_0)) == -11.0) || ((x_3 + (-1.0 * _x_x_0)) == -10.0))) && ((((x_1 + (-1.0 * _x_x_1)) <= -13.0) && ((x_2 + (-1.0 * _x_x_1)) <= -14.0)) && (((x_1 + (-1.0 * _x_x_1)) == -13.0) || ((x_2 + (-1.0 * _x_x_1)) == -14.0)))) && ((((x_0 + (-1.0 * _x_x_2)) <= -2.0) && ((x_2 + (-1.0 * _x_x_2)) <= -19.0)) && (((x_0 + (-1.0 * _x_x_2)) == -2.0) || ((x_2 + (-1.0 * _x_x_2)) == -19.0)))) && ((((x_0 + (-1.0 * _x_x_3)) <= -11.0) && ((x_3 + (-1.0 * _x_x_3)) <= -19.0)) && (((x_0 + (-1.0 * _x_x_3)) == -11.0) || ((x_3 + (-1.0 * _x_x_3)) == -19.0)))) && ((_EL_U_94 == (_x__EL_U_94 || ( !(2.0 <= (_x_x_0 + (-1.0 * _x_x_2)))))) && (_EL_X_85 == ((_x_x_2 + (-1.0 * _x_x_3)) <= 1.0))));
    _EL_X_85 = _x__EL_X_85;
    _EL_U_94 = _x__EL_U_94;
    x_2 = _x_x_2;
    x_0 = _x_x_0;
    x_3 = _x_x_3;
    x_1 = _x_x_1;

  }
}
