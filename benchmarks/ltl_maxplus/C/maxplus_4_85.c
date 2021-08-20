extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);
typedef enum {false, true} bool;
bool __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}

int main()
{
bool _J121, _x__J121;
bool _J113, _x__J113;
bool _EL_U_94, _x__EL_U_94;
float x_3, _x_x_3;
float x_0, _x_x_0;
bool _EL_U_96, _x__EL_U_96;
float x_2, _x_x_2;
float x_1, _x_x_1;

  int __steps_to_fair = __VERIFIER_nondet_int();
  _J121 = __VERIFIER_nondet_bool();
  _J113 = __VERIFIER_nondet_bool();
  _EL_U_94 = __VERIFIER_nondet_bool();
  x_3 = __VERIFIER_nondet_float();
  x_0 = __VERIFIER_nondet_float();
  _EL_U_96 = __VERIFIER_nondet_bool();
  x_2 = __VERIFIER_nondet_float();
  x_1 = __VERIFIER_nondet_float();

  bool __ok = (1 && ((( !(( !(( !(-20.0 <= (x_1 + (-1.0 * x_2)))) || _EL_U_96)) || (( !((x_0 + (-1.0 * x_3)) <= 12.0)) || _EL_U_94))) && ( !_J113)) && ( !_J121)));
  while (__steps_to_fair >= 0 && __ok) {
    if ((_J113 && _J121)) {
      __steps_to_fair = __VERIFIER_nondet_int();
    } else {
      __steps_to_fair--;
    }
    _x__J121 = __VERIFIER_nondet_bool();
    _x__J113 = __VERIFIER_nondet_bool();
    _x__EL_U_94 = __VERIFIER_nondet_bool();
    _x_x_3 = __VERIFIER_nondet_float();
    _x_x_0 = __VERIFIER_nondet_float();
    _x__EL_U_96 = __VERIFIER_nondet_bool();
    _x_x_2 = __VERIFIER_nondet_float();
    _x_x_1 = __VERIFIER_nondet_float();

    __ok = ((((((((x_2 + (-1.0 * _x_x_0)) <= -7.0) && ((x_3 + (-1.0 * _x_x_0)) <= -6.0)) && (((x_2 + (-1.0 * _x_x_0)) == -7.0) || ((x_3 + (-1.0 * _x_x_0)) == -6.0))) && ((((x_0 + (-1.0 * _x_x_1)) <= -20.0) && ((x_2 + (-1.0 * _x_x_1)) <= -19.0)) && (((x_0 + (-1.0 * _x_x_1)) == -20.0) || ((x_2 + (-1.0 * _x_x_1)) == -19.0)))) && ((((x_1 + (-1.0 * _x_x_2)) <= -9.0) && ((x_3 + (-1.0 * _x_x_2)) <= -5.0)) && (((x_1 + (-1.0 * _x_x_2)) == -9.0) || ((x_3 + (-1.0 * _x_x_2)) == -5.0)))) && ((((x_2 + (-1.0 * _x_x_3)) <= -6.0) && ((x_3 + (-1.0 * _x_x_3)) <= -2.0)) && (((x_2 + (-1.0 * _x_x_3)) == -6.0) || ((x_3 + (-1.0 * _x_x_3)) == -2.0)))) && ((((_EL_U_96 == (_x__EL_U_96 || ( !(-20.0 <= (_x_x_1 + (-1.0 * _x_x_2)))))) && (_EL_U_94 == (_x__EL_U_94 || ( !((_x_x_0 + (-1.0 * _x_x_3)) <= 12.0))))) && (_x__J113 == (( !(_J113 && _J121)) && ((_J113 && _J121) || ((( !(-20.0 <= (x_1 + (-1.0 * x_2)))) || ( !(( !(-20.0 <= (x_1 + (-1.0 * x_2)))) || _EL_U_96))) || _J113))))) && (_x__J121 == (( !(_J113 && _J121)) && ((_J113 && _J121) || ((( !((x_0 + (-1.0 * x_3)) <= 12.0)) || ( !(( !((x_0 + (-1.0 * x_3)) <= 12.0)) || _EL_U_94))) || _J121))))));
    _J121 = _x__J121;
    _J113 = _x__J113;
    _EL_U_94 = _x__EL_U_94;
    x_3 = _x_x_3;
    x_0 = _x_x_0;
    _EL_U_96 = _x__EL_U_96;
    x_2 = _x_x_2;
    x_1 = _x_x_1;

  }
}
