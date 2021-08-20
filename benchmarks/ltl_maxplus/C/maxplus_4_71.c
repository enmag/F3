extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);
typedef enum {false, true} bool;
bool __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}

int main()
{
bool _J126, _x__J126;
bool _J120, _x__J120;
bool _EL_U_101, _x__EL_U_101;
float x_3, _x_x_3;
float x_0, _x_x_0;
bool _EL_U_103, _x__EL_U_103;
float x_2, _x_x_2;
float x_1, _x_x_1;

  int __steps_to_fair = __VERIFIER_nondet_int();
  _J126 = __VERIFIER_nondet_bool();
  _J120 = __VERIFIER_nondet_bool();
  _EL_U_101 = __VERIFIER_nondet_bool();
  x_3 = __VERIFIER_nondet_float();
  x_0 = __VERIFIER_nondet_float();
  _EL_U_103 = __VERIFIER_nondet_bool();
  x_2 = __VERIFIER_nondet_float();
  x_1 = __VERIFIER_nondet_float();

  bool __ok = (1 && ((( !(( !(8.0 <= (x_1 + (-1.0 * x_2)))) && ( !(_EL_U_103 || ( !(( !(-19.0 <= (x_0 + (-1.0 * x_3)))) || _EL_U_101)))))) && ( !_J120)) && ( !_J126)));
  while (__steps_to_fair >= 0 && __ok) {
    if ((_J120 && _J126)) {
      __steps_to_fair = __VERIFIER_nondet_int();
    } else {
      __steps_to_fair--;
    }
    _x__J126 = __VERIFIER_nondet_bool();
    _x__J120 = __VERIFIER_nondet_bool();
    _x__EL_U_101 = __VERIFIER_nondet_bool();
    _x_x_3 = __VERIFIER_nondet_float();
    _x_x_0 = __VERIFIER_nondet_float();
    _x__EL_U_103 = __VERIFIER_nondet_bool();
    _x_x_2 = __VERIFIER_nondet_float();
    _x_x_1 = __VERIFIER_nondet_float();

    __ok = ((((((((x_1 + (-1.0 * _x_x_0)) <= -1.0) && ((x_3 + (-1.0 * _x_x_0)) <= -20.0)) && (((x_1 + (-1.0 * _x_x_0)) == -1.0) || ((x_3 + (-1.0 * _x_x_0)) == -20.0))) && ((((x_0 + (-1.0 * _x_x_1)) <= -7.0) && ((x_2 + (-1.0 * _x_x_1)) <= -6.0)) && (((x_0 + (-1.0 * _x_x_1)) == -7.0) || ((x_2 + (-1.0 * _x_x_1)) == -6.0)))) && ((((x_0 + (-1.0 * _x_x_2)) <= -9.0) && ((x_1 + (-1.0 * _x_x_2)) <= -15.0)) && (((x_0 + (-1.0 * _x_x_2)) == -9.0) || ((x_1 + (-1.0 * _x_x_2)) == -15.0)))) && ((((x_1 + (-1.0 * _x_x_3)) <= -5.0) && ((x_3 + (-1.0 * _x_x_3)) <= -1.0)) && (((x_1 + (-1.0 * _x_x_3)) == -5.0) || ((x_3 + (-1.0 * _x_x_3)) == -1.0)))) && ((((_EL_U_101 == (_x__EL_U_101 || ( !(-19.0 <= (_x_x_0 + (-1.0 * _x_x_3)))))) && (_EL_U_103 == (_x__EL_U_103 || ( !(_x__EL_U_101 || ( !(-19.0 <= (_x_x_0 + (-1.0 * _x_x_3))))))))) && (_x__J120 == (( !(_J120 && _J126)) && ((_J120 && _J126) || ((( !(-19.0 <= (x_0 + (-1.0 * x_3)))) || ( !(( !(-19.0 <= (x_0 + (-1.0 * x_3)))) || _EL_U_101))) || _J120))))) && (_x__J126 == (( !(_J120 && _J126)) && ((_J120 && _J126) || ((( !(( !(-19.0 <= (x_0 + (-1.0 * x_3)))) || _EL_U_101)) || ( !(_EL_U_103 || ( !(( !(-19.0 <= (x_0 + (-1.0 * x_3)))) || _EL_U_101))))) || _J126))))));
    _J126 = _x__J126;
    _J120 = _x__J120;
    _EL_U_101 = _x__EL_U_101;
    x_3 = _x_x_3;
    x_0 = _x_x_0;
    _EL_U_103 = _x__EL_U_103;
    x_2 = _x_x_2;
    x_1 = _x_x_1;

  }
}
