extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);
typedef enum {false, true} bool;
bool __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}

int main()
{
float x_3, _x_x_3;
bool _J121, _x__J121;
bool _J115, _x__J115;
bool _EL_U_98, _x__EL_U_98;
float x_1, _x_x_1;
float x_0, _x_x_0;
bool _EL_U_100, _x__EL_U_100;
float x_2, _x_x_2;

  int __steps_to_fair = __VERIFIER_nondet_int();
  x_3 = __VERIFIER_nondet_float();
  _J121 = __VERIFIER_nondet_bool();
  _J115 = __VERIFIER_nondet_bool();
  _EL_U_98 = __VERIFIER_nondet_bool();
  x_1 = __VERIFIER_nondet_float();
  x_0 = __VERIFIER_nondet_float();
  _EL_U_100 = __VERIFIER_nondet_bool();
  x_2 = __VERIFIER_nondet_float();

  bool __ok = (1 && ((( !(((x_1 + (-1.0 * x_2)) <= 19.0) && (_EL_U_100 || ( !((17.0 <= (x_0 + (-1.0 * x_1))) || _EL_U_98))))) && ( !_J115)) && ( !_J121)));
  while (__steps_to_fair >= 0 && __ok) {
    if ((_J115 && _J121)) {
      __steps_to_fair = __VERIFIER_nondet_int();
    } else {
      __steps_to_fair--;
    }
    _x_x_3 = __VERIFIER_nondet_float();
    _x__J121 = __VERIFIER_nondet_bool();
    _x__J115 = __VERIFIER_nondet_bool();
    _x__EL_U_98 = __VERIFIER_nondet_bool();
    _x_x_1 = __VERIFIER_nondet_float();
    _x_x_0 = __VERIFIER_nondet_float();
    _x__EL_U_100 = __VERIFIER_nondet_bool();
    _x_x_2 = __VERIFIER_nondet_float();

    __ok = ((((((((x_1 + (-1.0 * _x_x_0)) <= -4.0) && ((x_2 + (-1.0 * _x_x_0)) <= -16.0)) && (((x_1 + (-1.0 * _x_x_0)) == -4.0) || ((x_2 + (-1.0 * _x_x_0)) == -16.0))) && ((((x_2 + (-1.0 * _x_x_1)) <= -19.0) && ((x_3 + (-1.0 * _x_x_1)) <= -2.0)) && (((x_2 + (-1.0 * _x_x_1)) == -19.0) || ((x_3 + (-1.0 * _x_x_1)) == -2.0)))) && ((((x_0 + (-1.0 * _x_x_2)) <= -13.0) && ((x_1 + (-1.0 * _x_x_2)) <= -16.0)) && (((x_0 + (-1.0 * _x_x_2)) == -13.0) || ((x_1 + (-1.0 * _x_x_2)) == -16.0)))) && ((((x_0 + (-1.0 * _x_x_3)) <= -10.0) && ((x_2 + (-1.0 * _x_x_3)) <= -18.0)) && (((x_0 + (-1.0 * _x_x_3)) == -10.0) || ((x_2 + (-1.0 * _x_x_3)) == -18.0)))) && ((((_EL_U_98 == (_x__EL_U_98 || (17.0 <= (_x_x_0 + (-1.0 * _x_x_1))))) && (_EL_U_100 == (_x__EL_U_100 || ( !(_x__EL_U_98 || (17.0 <= (_x_x_0 + (-1.0 * _x_x_1)))))))) && (_x__J115 == (( !(_J115 && _J121)) && ((_J115 && _J121) || (((17.0 <= (x_0 + (-1.0 * x_1))) || ( !((17.0 <= (x_0 + (-1.0 * x_1))) || _EL_U_98))) || _J115))))) && (_x__J121 == (( !(_J115 && _J121)) && ((_J115 && _J121) || ((( !((17.0 <= (x_0 + (-1.0 * x_1))) || _EL_U_98)) || ( !(_EL_U_100 || ( !((17.0 <= (x_0 + (-1.0 * x_1))) || _EL_U_98))))) || _J121))))));
    x_3 = _x_x_3;
    _J121 = _x__J121;
    _J115 = _x__J115;
    _EL_U_98 = _x__EL_U_98;
    x_1 = _x_x_1;
    x_0 = _x_x_0;
    _EL_U_100 = _x__EL_U_100;
    x_2 = _x_x_2;

  }
}
