extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);
typedef enum {false, true} bool;
bool __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}

int main()
{
bool _EL_U_101, _x__EL_U_101;
bool _J130, _x__J130;
bool _J118, _x__J118;
bool _EL_X_102, _x__EL_X_102;
bool _EL_U_104, _x__EL_U_104;
float x_1, _x_x_1;
float x_0, _x_x_0;
float x_3, _x_x_3;
float x_2, _x_x_2;

  int __steps_to_fair = __VERIFIER_nondet_int();
  _EL_U_101 = __VERIFIER_nondet_bool();
  _J130 = __VERIFIER_nondet_bool();
  _J118 = __VERIFIER_nondet_bool();
  _EL_X_102 = __VERIFIER_nondet_bool();
  _EL_U_104 = __VERIFIER_nondet_bool();
  x_1 = __VERIFIER_nondet_float();
  x_0 = __VERIFIER_nondet_float();
  x_3 = __VERIFIER_nondet_float();
  x_2 = __VERIFIER_nondet_float();

  bool __ok = (1 && ((((20.0 <= (x_0 + (-1.0 * x_1))) || (_EL_U_104 && ( !_EL_X_102))) && ( !_J118)) && ( !_J130)));
  while (__steps_to_fair >= 0 && __ok) {
    if ((_J118 && _J130)) {
      __steps_to_fair = __VERIFIER_nondet_int();
    } else {
      __steps_to_fair--;
    }
    _x__EL_U_101 = __VERIFIER_nondet_bool();
    _x__J130 = __VERIFIER_nondet_bool();
    _x__J118 = __VERIFIER_nondet_bool();
    _x__EL_X_102 = __VERIFIER_nondet_bool();
    _x__EL_U_104 = __VERIFIER_nondet_bool();
    _x_x_1 = __VERIFIER_nondet_float();
    _x_x_0 = __VERIFIER_nondet_float();
    _x_x_3 = __VERIFIER_nondet_float();
    _x_x_2 = __VERIFIER_nondet_float();

    __ok = ((((((((x_0 + (-1.0 * _x_x_0)) <= -6.0) && ((x_2 + (-1.0 * _x_x_0)) <= -19.0)) && (((x_0 + (-1.0 * _x_x_0)) == -6.0) || ((x_2 + (-1.0 * _x_x_0)) == -19.0))) && ((((x_1 + (-1.0 * _x_x_1)) <= -14.0) && ((x_3 + (-1.0 * _x_x_1)) <= -8.0)) && (((x_1 + (-1.0 * _x_x_1)) == -14.0) || ((x_3 + (-1.0 * _x_x_1)) == -8.0)))) && ((((x_0 + (-1.0 * _x_x_2)) <= -10.0) && ((x_1 + (-1.0 * _x_x_2)) <= -16.0)) && (((x_0 + (-1.0 * _x_x_2)) == -10.0) || ((x_1 + (-1.0 * _x_x_2)) == -16.0)))) && ((((x_0 + (-1.0 * _x_x_3)) <= -16.0) && ((x_2 + (-1.0 * _x_x_3)) <= -17.0)) && (((x_0 + (-1.0 * _x_x_3)) == -16.0) || ((x_2 + (-1.0 * _x_x_3)) == -17.0)))) && ((((_EL_U_104 == ((_x__EL_U_104 && ( !_x__EL_X_102)) || (20.0 <= (_x_x_0 + (-1.0 * _x_x_1))))) && ((_EL_U_101 == (_x__EL_U_101 || ((_x_x_1 + (-1.0 * _x_x_2)) <= -4.0))) && (_EL_X_102 == (_x__EL_U_101 || ((_x_x_1 + (-1.0 * _x_x_2)) <= -4.0))))) && (_x__J118 == (( !(_J118 && _J130)) && ((_J118 && _J130) || ((((x_1 + (-1.0 * x_2)) <= -4.0) || ( !(((x_1 + (-1.0 * x_2)) <= -4.0) || _EL_U_101))) || _J118))))) && (_x__J130 == (( !(_J118 && _J130)) && ((_J118 && _J130) || (((20.0 <= (x_0 + (-1.0 * x_1))) || ( !((20.0 <= (x_0 + (-1.0 * x_1))) || (_EL_U_104 && ( !_EL_X_102))))) || _J130))))));
    _EL_U_101 = _x__EL_U_101;
    _J130 = _x__J130;
    _J118 = _x__J118;
    _EL_X_102 = _x__EL_X_102;
    _EL_U_104 = _x__EL_U_104;
    x_1 = _x_x_1;
    x_0 = _x_x_0;
    x_3 = _x_x_3;
    x_2 = _x_x_2;

  }
}
