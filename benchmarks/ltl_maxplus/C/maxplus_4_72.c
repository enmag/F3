extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);
typedef enum {false, true} bool;
bool __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}

int main()
{
bool _J126, _x__J126;
bool _J116, _x__J116;
float x_2, _x_x_2;
bool _EL_X_102, _x__EL_X_102;
bool _EL_U_101, _x__EL_U_101;
float x_3, _x_x_3;
float x_1, _x_x_1;
float x_0, _x_x_0;
bool _EL_U_99, _x__EL_U_99;

  int __steps_to_fair = __VERIFIER_nondet_int();
  _J126 = __VERIFIER_nondet_bool();
  _J116 = __VERIFIER_nondet_bool();
  x_2 = __VERIFIER_nondet_float();
  _EL_X_102 = __VERIFIER_nondet_bool();
  _EL_U_101 = __VERIFIER_nondet_bool();
  x_3 = __VERIFIER_nondet_float();
  x_1 = __VERIFIER_nondet_float();
  x_0 = __VERIFIER_nondet_float();
  _EL_U_99 = __VERIFIER_nondet_bool();

  bool __ok = (1 && ((_EL_X_102 && ( !_J116)) && ( !_J126)));
  while (__steps_to_fair >= 0 && __ok) {
    if ((_J116 && _J126)) {
      __steps_to_fair = __VERIFIER_nondet_int();
    } else {
      __steps_to_fair--;
    }
    _x__J126 = __VERIFIER_nondet_bool();
    _x__J116 = __VERIFIER_nondet_bool();
    _x_x_2 = __VERIFIER_nondet_float();
    _x__EL_X_102 = __VERIFIER_nondet_bool();
    _x__EL_U_101 = __VERIFIER_nondet_bool();
    _x_x_3 = __VERIFIER_nondet_float();
    _x_x_1 = __VERIFIER_nondet_float();
    _x_x_0 = __VERIFIER_nondet_float();
    _x__EL_U_99 = __VERIFIER_nondet_bool();

    __ok = ((((((((x_1 + (-1.0 * _x_x_0)) <= -17.0) && ((x_2 + (-1.0 * _x_x_0)) <= -3.0)) && (((x_1 + (-1.0 * _x_x_0)) == -17.0) || ((x_2 + (-1.0 * _x_x_0)) == -3.0))) && ((((x_0 + (-1.0 * _x_x_1)) <= -15.0) && ((x_1 + (-1.0 * _x_x_1)) <= -12.0)) && (((x_0 + (-1.0 * _x_x_1)) == -15.0) || ((x_1 + (-1.0 * _x_x_1)) == -12.0)))) && ((((x_2 + (-1.0 * _x_x_2)) <= -20.0) && ((x_3 + (-1.0 * _x_x_2)) <= -7.0)) && (((x_2 + (-1.0 * _x_x_2)) == -20.0) || ((x_3 + (-1.0 * _x_x_2)) == -7.0)))) && ((((x_0 + (-1.0 * _x_x_3)) <= -15.0) && ((x_3 + (-1.0 * _x_x_3)) <= -10.0)) && (((x_0 + (-1.0 * _x_x_3)) == -15.0) || ((x_3 + (-1.0 * _x_x_3)) == -10.0)))) && ((((_EL_X_102 == ((_x__EL_U_99 || (-11.0 <= (_x_x_2 + (-1.0 * _x_x_3)))) || (_x__EL_U_101 && ( !(-13.0 <= (_x_x_1 + (-1.0 * _x_x_2))))))) && ((_EL_U_99 == (_x__EL_U_99 || (-11.0 <= (_x_x_2 + (-1.0 * _x_x_3))))) && (_EL_U_101 == ((_x__EL_U_99 || (-11.0 <= (_x_x_2 + (-1.0 * _x_x_3)))) || (_x__EL_U_101 && ( !(-13.0 <= (_x_x_1 + (-1.0 * _x_x_2))))))))) && (_x__J116 == (( !(_J116 && _J126)) && ((_J116 && _J126) || (((-11.0 <= (x_2 + (-1.0 * x_3))) || ( !((-11.0 <= (x_2 + (-1.0 * x_3))) || _EL_U_99))) || _J116))))) && (_x__J126 == (( !(_J116 && _J126)) && ((_J116 && _J126) || ((((-11.0 <= (x_2 + (-1.0 * x_3))) || _EL_U_99) || ( !(((-11.0 <= (x_2 + (-1.0 * x_3))) || _EL_U_99) || (( !(-13.0 <= (x_1 + (-1.0 * x_2)))) && _EL_U_101)))) || _J126))))));
    _J126 = _x__J126;
    _J116 = _x__J116;
    x_2 = _x_x_2;
    _EL_X_102 = _x__EL_X_102;
    _EL_U_101 = _x__EL_U_101;
    x_3 = _x_x_3;
    x_1 = _x_x_1;
    x_0 = _x_x_0;
    _EL_U_99 = _x__EL_U_99;

  }
}
