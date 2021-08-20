extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);
typedef enum {false, true} bool;
bool __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}

int main()
{
bool _J129, _x__J129;
bool _J121, _x__J121;
bool _EL_U_99, _x__EL_U_99;
float x_3, _x_x_3;
float x_1, _x_x_1;
float x_0, _x_x_0;
bool _EL_U_101, _x__EL_U_101;
bool _EL_X_94, _x__EL_X_94;
float x_2, _x_x_2;

  int __steps_to_fair = __VERIFIER_nondet_int();
  _J129 = __VERIFIER_nondet_bool();
  _J121 = __VERIFIER_nondet_bool();
  _EL_U_99 = __VERIFIER_nondet_bool();
  x_3 = __VERIFIER_nondet_float();
  x_1 = __VERIFIER_nondet_float();
  x_0 = __VERIFIER_nondet_float();
  _EL_U_101 = __VERIFIER_nondet_bool();
  _EL_X_94 = __VERIFIER_nondet_bool();
  x_2 = __VERIFIER_nondet_float();

  bool __ok = (1 && (((( !_EL_X_94) || (_EL_U_101 && (( !((x_1 + (-1.0 * x_3)) <= -9.0)) || _EL_U_99))) && ( !_J121)) && ( !_J129)));
  while (__steps_to_fair >= 0 && __ok) {
    if ((_J121 && _J129)) {
      __steps_to_fair = __VERIFIER_nondet_int();
    } else {
      __steps_to_fair--;
    }
    _x__J129 = __VERIFIER_nondet_bool();
    _x__J121 = __VERIFIER_nondet_bool();
    _x__EL_U_99 = __VERIFIER_nondet_bool();
    _x_x_3 = __VERIFIER_nondet_float();
    _x_x_1 = __VERIFIER_nondet_float();
    _x_x_0 = __VERIFIER_nondet_float();
    _x__EL_U_101 = __VERIFIER_nondet_bool();
    _x__EL_X_94 = __VERIFIER_nondet_bool();
    _x_x_2 = __VERIFIER_nondet_float();

    __ok = ((((((((x_0 + (-1.0 * _x_x_0)) <= -12.0) && ((x_2 + (-1.0 * _x_x_0)) <= -4.0)) && (((x_0 + (-1.0 * _x_x_0)) == -12.0) || ((x_2 + (-1.0 * _x_x_0)) == -4.0))) && ((((x_0 + (-1.0 * _x_x_1)) <= -13.0) && ((x_3 + (-1.0 * _x_x_1)) <= -5.0)) && (((x_0 + (-1.0 * _x_x_1)) == -13.0) || ((x_3 + (-1.0 * _x_x_1)) == -5.0)))) && ((((x_0 + (-1.0 * _x_x_2)) <= -1.0) && ((x_1 + (-1.0 * _x_x_2)) <= -8.0)) && (((x_0 + (-1.0 * _x_x_2)) == -1.0) || ((x_1 + (-1.0 * _x_x_2)) == -8.0)))) && ((((x_1 + (-1.0 * _x_x_3)) <= -19.0) && ((x_2 + (-1.0 * _x_x_3)) <= -12.0)) && (((x_1 + (-1.0 * _x_x_3)) == -19.0) || ((x_2 + (-1.0 * _x_x_3)) == -12.0)))) && ((((_EL_U_101 == ((_x__EL_U_101 && (_x__EL_U_99 || ( !((_x_x_1 + (-1.0 * _x_x_3)) <= -9.0)))) || ( !_x__EL_X_94))) && ((_EL_X_94 == (-18.0 <= (_x_x_1 + (-1.0 * _x_x_2)))) && (_EL_U_99 == (_x__EL_U_99 || ( !((_x_x_1 + (-1.0 * _x_x_3)) <= -9.0)))))) && (_x__J121 == (( !(_J121 && _J129)) && ((_J121 && _J129) || ((( !((x_1 + (-1.0 * x_3)) <= -9.0)) || ( !(( !((x_1 + (-1.0 * x_3)) <= -9.0)) || _EL_U_99))) || _J121))))) && (_x__J129 == (( !(_J121 && _J129)) && ((_J121 && _J129) || ((( !_EL_X_94) || ( !(( !_EL_X_94) || (_EL_U_101 && (( !((x_1 + (-1.0 * x_3)) <= -9.0)) || _EL_U_99))))) || _J129))))));
    _J129 = _x__J129;
    _J121 = _x__J121;
    _EL_U_99 = _x__EL_U_99;
    x_3 = _x_x_3;
    x_1 = _x_x_1;
    x_0 = _x_x_0;
    _EL_U_101 = _x__EL_U_101;
    _EL_X_94 = _x__EL_X_94;
    x_2 = _x_x_2;

  }
}
