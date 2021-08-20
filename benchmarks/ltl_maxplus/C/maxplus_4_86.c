extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);
typedef enum {false, true} bool;
bool __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}

int main()
{
bool _J113, _x__J113;
bool _J107, _x__J107;
float x_0, _x_x_0;
bool _EL_U_89, _x__EL_U_89;
float x_2, _x_x_2;
float x_1, _x_x_1;
bool _EL_U_91, _x__EL_U_91;
float x_3, _x_x_3;

  int __steps_to_fair = __VERIFIER_nondet_int();
  _J113 = __VERIFIER_nondet_bool();
  _J107 = __VERIFIER_nondet_bool();
  x_0 = __VERIFIER_nondet_float();
  _EL_U_89 = __VERIFIER_nondet_bool();
  x_2 = __VERIFIER_nondet_float();
  x_1 = __VERIFIER_nondet_float();
  _EL_U_91 = __VERIFIER_nondet_bool();
  x_3 = __VERIFIER_nondet_float();

  bool __ok = (1 && ((( !(((x_1 + (-1.0 * x_2)) <= -4.0) && ( !(_EL_U_91 || ( !(((x_1 + (-1.0 * x_2)) <= -9.0) || _EL_U_89)))))) && ( !_J107)) && ( !_J113)));
  while (__steps_to_fair >= 0 && __ok) {
    if ((_J107 && _J113)) {
      __steps_to_fair = __VERIFIER_nondet_int();
    } else {
      __steps_to_fair--;
    }
    _x__J113 = __VERIFIER_nondet_bool();
    _x__J107 = __VERIFIER_nondet_bool();
    _x_x_0 = __VERIFIER_nondet_float();
    _x__EL_U_89 = __VERIFIER_nondet_bool();
    _x_x_2 = __VERIFIER_nondet_float();
    _x_x_1 = __VERIFIER_nondet_float();
    _x__EL_U_91 = __VERIFIER_nondet_bool();
    _x_x_3 = __VERIFIER_nondet_float();

    __ok = ((((((((x_1 + (-1.0 * _x_x_0)) <= -9.0) && ((x_2 + (-1.0 * _x_x_0)) <= -10.0)) && (((x_1 + (-1.0 * _x_x_0)) == -9.0) || ((x_2 + (-1.0 * _x_x_0)) == -10.0))) && ((((x_2 + (-1.0 * _x_x_1)) <= -16.0) && ((x_3 + (-1.0 * _x_x_1)) <= -5.0)) && (((x_2 + (-1.0 * _x_x_1)) == -16.0) || ((x_3 + (-1.0 * _x_x_1)) == -5.0)))) && ((((x_0 + (-1.0 * _x_x_2)) <= -6.0) && ((x_1 + (-1.0 * _x_x_2)) <= -4.0)) && (((x_0 + (-1.0 * _x_x_2)) == -6.0) || ((x_1 + (-1.0 * _x_x_2)) == -4.0)))) && ((((x_0 + (-1.0 * _x_x_3)) <= -6.0) && ((x_1 + (-1.0 * _x_x_3)) <= -16.0)) && (((x_0 + (-1.0 * _x_x_3)) == -6.0) || ((x_1 + (-1.0 * _x_x_3)) == -16.0)))) && ((((_EL_U_89 == (_x__EL_U_89 || ((_x_x_1 + (-1.0 * _x_x_2)) <= -9.0))) && (_EL_U_91 == (_x__EL_U_91 || ( !(_x__EL_U_89 || ((_x_x_1 + (-1.0 * _x_x_2)) <= -9.0)))))) && (_x__J107 == (( !(_J107 && _J113)) && ((_J107 && _J113) || ((((x_1 + (-1.0 * x_2)) <= -9.0) || ( !(((x_1 + (-1.0 * x_2)) <= -9.0) || _EL_U_89))) || _J107))))) && (_x__J113 == (( !(_J107 && _J113)) && ((_J107 && _J113) || ((( !(((x_1 + (-1.0 * x_2)) <= -9.0) || _EL_U_89)) || ( !(_EL_U_91 || ( !(((x_1 + (-1.0 * x_2)) <= -9.0) || _EL_U_89))))) || _J113))))));
    _J113 = _x__J113;
    _J107 = _x__J107;
    x_0 = _x_x_0;
    _EL_U_89 = _x__EL_U_89;
    x_2 = _x_x_2;
    x_1 = _x_x_1;
    _EL_U_91 = _x__EL_U_91;
    x_3 = _x_x_3;

  }
}
