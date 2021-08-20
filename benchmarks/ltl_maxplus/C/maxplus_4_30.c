extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);
typedef enum {false, true} bool;
bool __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}

int main()
{
bool _J130, _x__J130;
float x_0, _x_x_0;
bool _J119, _x__J119;
bool _EL_U_102, _x__EL_U_102;
bool _EL_X_89, _x__EL_X_89;
bool _EL_U_100, _x__EL_U_100;
float x_2, _x_x_2;
float x_1, _x_x_1;
float x_3, _x_x_3;

  int __steps_to_fair = __VERIFIER_nondet_int();
  _J130 = __VERIFIER_nondet_bool();
  x_0 = __VERIFIER_nondet_float();
  _J119 = __VERIFIER_nondet_bool();
  _EL_U_102 = __VERIFIER_nondet_bool();
  _EL_X_89 = __VERIFIER_nondet_bool();
  _EL_U_100 = __VERIFIER_nondet_bool();
  x_2 = __VERIFIER_nondet_float();
  x_1 = __VERIFIER_nondet_float();
  x_3 = __VERIFIER_nondet_float();

  bool __ok = (1 && ((( !(( !(( !((x_1 + (-1.0 * x_2)) <= -10.0)) || _EL_U_100)) || (_EL_X_89 && _EL_U_102))) && ( !_J119)) && ( !_J130)));
  while (__steps_to_fair >= 0 && __ok) {
    if ((_J119 && _J130)) {
      __steps_to_fair = __VERIFIER_nondet_int();
    } else {
      __steps_to_fair--;
    }
    _x__J130 = __VERIFIER_nondet_bool();
    _x_x_0 = __VERIFIER_nondet_float();
    _x__J119 = __VERIFIER_nondet_bool();
    _x__EL_U_102 = __VERIFIER_nondet_bool();
    _x__EL_X_89 = __VERIFIER_nondet_bool();
    _x__EL_U_100 = __VERIFIER_nondet_bool();
    _x_x_2 = __VERIFIER_nondet_float();
    _x_x_1 = __VERIFIER_nondet_float();
    _x_x_3 = __VERIFIER_nondet_float();

    __ok = ((((((((x_0 + (-1.0 * _x_x_0)) <= -17.0) && ((x_2 + (-1.0 * _x_x_0)) <= -4.0)) && (((x_0 + (-1.0 * _x_x_0)) == -17.0) || ((x_2 + (-1.0 * _x_x_0)) == -4.0))) && ((((x_0 + (-1.0 * _x_x_1)) <= -7.0) && ((x_3 + (-1.0 * _x_x_1)) <= -12.0)) && (((x_0 + (-1.0 * _x_x_1)) == -7.0) || ((x_3 + (-1.0 * _x_x_1)) == -12.0)))) && ((((x_1 + (-1.0 * _x_x_2)) <= -8.0) && ((x_2 + (-1.0 * _x_x_2)) <= -9.0)) && (((x_1 + (-1.0 * _x_x_2)) == -8.0) || ((x_2 + (-1.0 * _x_x_2)) == -9.0)))) && ((((x_0 + (-1.0 * _x_x_3)) <= -14.0) && ((x_1 + (-1.0 * _x_x_3)) <= -4.0)) && (((x_0 + (-1.0 * _x_x_3)) == -14.0) || ((x_1 + (-1.0 * _x_x_3)) == -4.0)))) && ((((_EL_U_102 == ((_x__EL_U_102 && _x__EL_X_89) || ( !(_x__EL_U_100 || ( !((_x_x_1 + (-1.0 * _x_x_2)) <= -10.0)))))) && ((_EL_U_100 == (_x__EL_U_100 || ( !((_x_x_1 + (-1.0 * _x_x_2)) <= -10.0)))) && (_EL_X_89 == ((_x_x_1 + (-1.0 * _x_x_3)) <= 20.0)))) && (_x__J119 == (( !(_J119 && _J130)) && ((_J119 && _J130) || ((( !((x_1 + (-1.0 * x_2)) <= -10.0)) || ( !(( !((x_1 + (-1.0 * x_2)) <= -10.0)) || _EL_U_100))) || _J119))))) && (_x__J130 == (( !(_J119 && _J130)) && ((_J119 && _J130) || ((( !(( !((x_1 + (-1.0 * x_2)) <= -10.0)) || _EL_U_100)) || ( !(( !(( !((x_1 + (-1.0 * x_2)) <= -10.0)) || _EL_U_100)) || (_EL_X_89 && _EL_U_102)))) || _J130))))));
    _J130 = _x__J130;
    x_0 = _x_x_0;
    _J119 = _x__J119;
    _EL_U_102 = _x__EL_U_102;
    _EL_X_89 = _x__EL_X_89;
    _EL_U_100 = _x__EL_U_100;
    x_2 = _x_x_2;
    x_1 = _x_x_1;
    x_3 = _x_x_3;

  }
}
