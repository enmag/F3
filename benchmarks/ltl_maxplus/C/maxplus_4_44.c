extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);
typedef enum {false, true} bool;
bool __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}

int main()
{
bool _J128, _x__J128;
float x_1, _x_x_1;
bool _J117, _x__J117;
float x_0, _x_x_0;
bool _EL_X_102, _x__EL_X_102;
bool _EL_U_101, _x__EL_U_101;
float x_3, _x_x_3;
bool _EL_U_99, _x__EL_U_99;
float x_2, _x_x_2;

  int __steps_to_fair = __VERIFIER_nondet_int();
  _J128 = __VERIFIER_nondet_bool();
  x_1 = __VERIFIER_nondet_float();
  _J117 = __VERIFIER_nondet_bool();
  x_0 = __VERIFIER_nondet_float();
  _EL_X_102 = __VERIFIER_nondet_bool();
  _EL_U_101 = __VERIFIER_nondet_bool();
  x_3 = __VERIFIER_nondet_float();
  _EL_U_99 = __VERIFIER_nondet_bool();
  x_2 = __VERIFIER_nondet_float();

  bool __ok = (1 && ((( !_EL_X_102) && ( !_J117)) && ( !_J128)));
  while (__steps_to_fair >= 0 && __ok) {
    if ((_J117 && _J128)) {
      __steps_to_fair = __VERIFIER_nondet_int();
    } else {
      __steps_to_fair--;
    }
    _x__J128 = __VERIFIER_nondet_bool();
    _x_x_1 = __VERIFIER_nondet_float();
    _x__J117 = __VERIFIER_nondet_bool();
    _x_x_0 = __VERIFIER_nondet_float();
    _x__EL_X_102 = __VERIFIER_nondet_bool();
    _x__EL_U_101 = __VERIFIER_nondet_bool();
    _x_x_3 = __VERIFIER_nondet_float();
    _x__EL_U_99 = __VERIFIER_nondet_bool();
    _x_x_2 = __VERIFIER_nondet_float();

    __ok = ((((((((x_1 + (-1.0 * _x_x_0)) <= -5.0) && ((x_3 + (-1.0 * _x_x_0)) <= -15.0)) && (((x_1 + (-1.0 * _x_x_0)) == -5.0) || ((x_3 + (-1.0 * _x_x_0)) == -15.0))) && ((((x_0 + (-1.0 * _x_x_1)) <= -13.0) && ((x_3 + (-1.0 * _x_x_1)) <= -16.0)) && (((x_0 + (-1.0 * _x_x_1)) == -13.0) || ((x_3 + (-1.0 * _x_x_1)) == -16.0)))) && ((((x_0 + (-1.0 * _x_x_2)) <= -12.0) && ((x_2 + (-1.0 * _x_x_2)) <= -20.0)) && (((x_0 + (-1.0 * _x_x_2)) == -12.0) || ((x_2 + (-1.0 * _x_x_2)) == -20.0)))) && ((((x_2 + (-1.0 * _x_x_3)) <= -5.0) && ((x_3 + (-1.0 * _x_x_3)) <= -19.0)) && (((x_2 + (-1.0 * _x_x_3)) == -5.0) || ((x_3 + (-1.0 * _x_x_3)) == -19.0)))) && ((((_EL_X_102 == ((_x__EL_U_101 && ( !(-20.0 <= (_x_x_0 + (-1.0 * _x_x_1))))) || ( !(_x__EL_U_99 || (9.0 <= (_x_x_1 + (-1.0 * _x_x_2))))))) && ((_EL_U_99 == (_x__EL_U_99 || (9.0 <= (_x_x_1 + (-1.0 * _x_x_2))))) && (_EL_U_101 == ((_x__EL_U_101 && ( !(-20.0 <= (_x_x_0 + (-1.0 * _x_x_1))))) || ( !(_x__EL_U_99 || (9.0 <= (_x_x_1 + (-1.0 * _x_x_2))))))))) && (_x__J117 == (( !(_J117 && _J128)) && ((_J117 && _J128) || (((9.0 <= (x_1 + (-1.0 * x_2))) || ( !((9.0 <= (x_1 + (-1.0 * x_2))) || _EL_U_99))) || _J117))))) && (_x__J128 == (( !(_J117 && _J128)) && ((_J117 && _J128) || ((( !((9.0 <= (x_1 + (-1.0 * x_2))) || _EL_U_99)) || ( !(( !((9.0 <= (x_1 + (-1.0 * x_2))) || _EL_U_99)) || (( !(-20.0 <= (x_0 + (-1.0 * x_1)))) && _EL_U_101)))) || _J128))))));
    _J128 = _x__J128;
    x_1 = _x_x_1;
    _J117 = _x__J117;
    x_0 = _x_x_0;
    _EL_X_102 = _x__EL_X_102;
    _EL_U_101 = _x__EL_U_101;
    x_3 = _x_x_3;
    _EL_U_99 = _x__EL_U_99;
    x_2 = _x_x_2;

  }
}
