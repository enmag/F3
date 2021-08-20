extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);
typedef enum {false, true} bool;
bool __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}

int main()
{
float x_2, _x_x_2;
bool _EL_U_98, _x__EL_U_98;
bool _J131, _x__J131;
bool _J118, _x__J118;
bool _EL_U_102, _x__EL_U_102;
float x_1, _x_x_1;
float x_0, _x_x_0;
bool _EL_X_100, _x__EL_X_100;
float x_3, _x_x_3;

  int __steps_to_fair = __VERIFIER_nondet_int();
  x_2 = __VERIFIER_nondet_float();
  _EL_U_98 = __VERIFIER_nondet_bool();
  _J131 = __VERIFIER_nondet_bool();
  _J118 = __VERIFIER_nondet_bool();
  _EL_U_102 = __VERIFIER_nondet_bool();
  x_1 = __VERIFIER_nondet_float();
  x_0 = __VERIFIER_nondet_float();
  _EL_X_100 = __VERIFIER_nondet_bool();
  x_3 = __VERIFIER_nondet_float();

  bool __ok = (1 && (((( !_EL_X_100) || (( !(-3.0 <= (x_0 + (-1.0 * x_1)))) && _EL_U_102)) && ( !_J118)) && ( !_J131)));
  while (__steps_to_fair >= 0 && __ok) {
    if ((_J118 && _J131)) {
      __steps_to_fair = __VERIFIER_nondet_int();
    } else {
      __steps_to_fair--;
    }
    _x_x_2 = __VERIFIER_nondet_float();
    _x__EL_U_98 = __VERIFIER_nondet_bool();
    _x__J131 = __VERIFIER_nondet_bool();
    _x__J118 = __VERIFIER_nondet_bool();
    _x__EL_U_102 = __VERIFIER_nondet_bool();
    _x_x_1 = __VERIFIER_nondet_float();
    _x_x_0 = __VERIFIER_nondet_float();
    _x__EL_X_100 = __VERIFIER_nondet_bool();
    _x_x_3 = __VERIFIER_nondet_float();

    __ok = ((((((((x_2 + (-1.0 * _x_x_0)) <= -16.0) && ((x_3 + (-1.0 * _x_x_0)) <= -14.0)) && (((x_2 + (-1.0 * _x_x_0)) == -16.0) || ((x_3 + (-1.0 * _x_x_0)) == -14.0))) && ((((x_1 + (-1.0 * _x_x_1)) <= -8.0) && ((x_2 + (-1.0 * _x_x_1)) <= -20.0)) && (((x_1 + (-1.0 * _x_x_1)) == -8.0) || ((x_2 + (-1.0 * _x_x_1)) == -20.0)))) && ((((x_0 + (-1.0 * _x_x_2)) <= -16.0) && ((x_1 + (-1.0 * _x_x_2)) <= -18.0)) && (((x_0 + (-1.0 * _x_x_2)) == -16.0) || ((x_1 + (-1.0 * _x_x_2)) == -18.0)))) && ((((x_2 + (-1.0 * _x_x_3)) <= -6.0) && ((x_3 + (-1.0 * _x_x_3)) <= -19.0)) && (((x_2 + (-1.0 * _x_x_3)) == -6.0) || ((x_3 + (-1.0 * _x_x_3)) == -19.0)))) && ((((_EL_U_102 == ((_x__EL_U_102 && ( !(-3.0 <= (_x_x_0 + (-1.0 * _x_x_1))))) || ( !_x__EL_X_100))) && ((_EL_U_98 == (_x__EL_U_98 || ( !((_x_x_0 + (-1.0 * _x_x_1)) <= 12.0)))) && (_EL_X_100 == ( !(_x__EL_U_98 || ( !((_x_x_0 + (-1.0 * _x_x_1)) <= 12.0))))))) && (_x__J118 == (( !(_J118 && _J131)) && ((_J118 && _J131) || ((( !((x_0 + (-1.0 * x_1)) <= 12.0)) || ( !(( !((x_0 + (-1.0 * x_1)) <= 12.0)) || _EL_U_98))) || _J118))))) && (_x__J131 == (( !(_J118 && _J131)) && ((_J118 && _J131) || ((( !_EL_X_100) || ( !(( !_EL_X_100) || (( !(-3.0 <= (x_0 + (-1.0 * x_1)))) && _EL_U_102)))) || _J131))))));
    x_2 = _x_x_2;
    _EL_U_98 = _x__EL_U_98;
    _J131 = _x__J131;
    _J118 = _x__J118;
    _EL_U_102 = _x__EL_U_102;
    x_1 = _x_x_1;
    x_0 = _x_x_0;
    _EL_X_100 = _x__EL_X_100;
    x_3 = _x_x_3;

  }
}
