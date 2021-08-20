extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);
typedef enum {false, true} bool;
bool __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}

int main()
{
bool _EL_X_92, _x__EL_X_92;
bool _EL_X_97, _x__EL_X_97;
float x_1, _x_x_1;
float x_0, _x_x_0;
bool _EL_U_95, _x__EL_U_95;
float x_3, _x_x_3;
float x_2, _x_x_2;

  int __steps_to_fair = __VERIFIER_nondet_int();
  _EL_X_92 = __VERIFIER_nondet_bool();
  _EL_X_97 = __VERIFIER_nondet_bool();
  x_1 = __VERIFIER_nondet_float();
  x_0 = __VERIFIER_nondet_float();
  _EL_U_95 = __VERIFIER_nondet_bool();
  x_3 = __VERIFIER_nondet_float();
  x_2 = __VERIFIER_nondet_float();

  bool __ok = (1 && ( !(_EL_X_97 && _EL_X_92)));
  while (__steps_to_fair >= 0 && __ok) {
    if (((10.0 <= (x_2 + (-1.0 * x_3))) || ( !((10.0 <= (x_2 + (-1.0 * x_3))) || _EL_U_95)))) {
      __steps_to_fair = __VERIFIER_nondet_int();
    } else {
      __steps_to_fair--;
    }
    _x__EL_X_92 = __VERIFIER_nondet_bool();
    _x__EL_X_97 = __VERIFIER_nondet_bool();
    _x_x_1 = __VERIFIER_nondet_float();
    _x_x_0 = __VERIFIER_nondet_float();
    _x__EL_U_95 = __VERIFIER_nondet_bool();
    _x_x_3 = __VERIFIER_nondet_float();
    _x_x_2 = __VERIFIER_nondet_float();

    __ok = ((((((((x_1 + (-1.0 * _x_x_0)) <= -12.0) && ((x_3 + (-1.0 * _x_x_0)) <= -10.0)) && (((x_1 + (-1.0 * _x_x_0)) == -12.0) || ((x_3 + (-1.0 * _x_x_0)) == -10.0))) && ((((x_1 + (-1.0 * _x_x_1)) <= -11.0) && ((x_2 + (-1.0 * _x_x_1)) <= -14.0)) && (((x_1 + (-1.0 * _x_x_1)) == -11.0) || ((x_2 + (-1.0 * _x_x_1)) == -14.0)))) && ((((x_0 + (-1.0 * _x_x_2)) <= -6.0) && ((x_2 + (-1.0 * _x_x_2)) <= -15.0)) && (((x_0 + (-1.0 * _x_x_2)) == -6.0) || ((x_2 + (-1.0 * _x_x_2)) == -15.0)))) && ((((x_0 + (-1.0 * _x_x_3)) <= -17.0) && ((x_1 + (-1.0 * _x_x_3)) <= -10.0)) && (((x_0 + (-1.0 * _x_x_3)) == -17.0) || ((x_1 + (-1.0 * _x_x_3)) == -10.0)))) && ((_EL_X_92 == (-1.0 <= (_x_x_2 + (-1.0 * _x_x_3)))) && ((_EL_U_95 == (_x__EL_U_95 || (10.0 <= (_x_x_2 + (-1.0 * _x_x_3))))) && (_EL_X_97 == ( !(_x__EL_U_95 || (10.0 <= (_x_x_2 + (-1.0 * _x_x_3)))))))));
    _EL_X_92 = _x__EL_X_92;
    _EL_X_97 = _x__EL_X_97;
    x_1 = _x_x_1;
    x_0 = _x_x_0;
    _EL_U_95 = _x__EL_U_95;
    x_3 = _x_x_3;
    x_2 = _x_x_2;

  }
}
