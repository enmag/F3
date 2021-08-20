extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);
typedef enum {false, true} bool;
bool __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}

int main()
{
float x_3, _x_x_3;
bool _EL_U_96, _x__EL_U_96;
float x_2, _x_x_2;
float x_0, _x_x_0;
bool _EL_X_85, _x__EL_X_85;
float x_1, _x_x_1;

  int __steps_to_fair = __VERIFIER_nondet_int();
  x_3 = __VERIFIER_nondet_float();
  _EL_U_96 = __VERIFIER_nondet_bool();
  x_2 = __VERIFIER_nondet_float();
  x_0 = __VERIFIER_nondet_float();
  _EL_X_85 = __VERIFIER_nondet_bool();
  x_1 = __VERIFIER_nondet_float();

  bool __ok = (1 && ( !(_EL_X_85 || ( !((-6.0 <= (x_0 + (-1.0 * x_2))) || _EL_U_96)))));
  while (__steps_to_fair >= 0 && __ok) {
    if (((-6.0 <= (x_0 + (-1.0 * x_2))) || ( !((-6.0 <= (x_0 + (-1.0 * x_2))) || _EL_U_96)))) {
      __steps_to_fair = __VERIFIER_nondet_int();
    } else {
      __steps_to_fair--;
    }
    _x_x_3 = __VERIFIER_nondet_float();
    _x__EL_U_96 = __VERIFIER_nondet_bool();
    _x_x_2 = __VERIFIER_nondet_float();
    _x_x_0 = __VERIFIER_nondet_float();
    _x__EL_X_85 = __VERIFIER_nondet_bool();
    _x_x_1 = __VERIFIER_nondet_float();

    __ok = ((((((((x_2 + (-1.0 * _x_x_0)) <= -2.0) && ((x_3 + (-1.0 * _x_x_0)) <= -7.0)) && (((x_2 + (-1.0 * _x_x_0)) == -2.0) || ((x_3 + (-1.0 * _x_x_0)) == -7.0))) && ((((x_0 + (-1.0 * _x_x_1)) <= -17.0) && ((x_2 + (-1.0 * _x_x_1)) <= -5.0)) && (((x_0 + (-1.0 * _x_x_1)) == -17.0) || ((x_2 + (-1.0 * _x_x_1)) == -5.0)))) && ((((x_0 + (-1.0 * _x_x_2)) <= -8.0) && ((x_3 + (-1.0 * _x_x_2)) <= -1.0)) && (((x_0 + (-1.0 * _x_x_2)) == -8.0) || ((x_3 + (-1.0 * _x_x_2)) == -1.0)))) && ((((x_1 + (-1.0 * _x_x_3)) <= -14.0) && ((x_2 + (-1.0 * _x_x_3)) <= -14.0)) && (((x_1 + (-1.0 * _x_x_3)) == -14.0) || ((x_2 + (-1.0 * _x_x_3)) == -14.0)))) && ((_EL_U_96 == (_x__EL_U_96 || (-6.0 <= (_x_x_0 + (-1.0 * _x_x_2))))) && (_EL_X_85 == (13.0 <= (_x_x_1 + (-1.0 * _x_x_2))))));
    x_3 = _x_x_3;
    _EL_U_96 = _x__EL_U_96;
    x_2 = _x_x_2;
    x_0 = _x_x_0;
    _EL_X_85 = _x__EL_X_85;
    x_1 = _x_x_1;

  }
}
