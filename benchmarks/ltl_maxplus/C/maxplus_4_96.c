extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);
typedef enum {false, true} bool;
bool __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}

int main()
{
float x_3, _x_x_3;
bool _J124, _x__J124;
bool _J118, _x__J118;
bool _EL_X_98, _x__EL_X_98;
bool _EL_X_89, _x__EL_X_89;
float x_2, _x_x_2;
bool _EL_U_95, _x__EL_U_95;
bool _EL_U_97, _x__EL_U_97;
float x_1, _x_x_1;
float x_0, _x_x_0;

  int __steps_to_fair = __VERIFIER_nondet_int();
  x_3 = __VERIFIER_nondet_float();
  _J124 = __VERIFIER_nondet_bool();
  _J118 = __VERIFIER_nondet_bool();
  _EL_X_98 = __VERIFIER_nondet_bool();
  _EL_X_89 = __VERIFIER_nondet_bool();
  x_2 = __VERIFIER_nondet_float();
  _EL_U_95 = __VERIFIER_nondet_bool();
  _EL_U_97 = __VERIFIER_nondet_bool();
  x_1 = __VERIFIER_nondet_float();
  x_0 = __VERIFIER_nondet_float();

  bool __ok = (1 && ((( !_EL_X_98) && ( !_J118)) && ( !_J124)));
  while (__steps_to_fair >= 0 && __ok) {
    if ((_J118 && _J124)) {
      __steps_to_fair = __VERIFIER_nondet_int();
    } else {
      __steps_to_fair--;
    }
    _x_x_3 = __VERIFIER_nondet_float();
    _x__J124 = __VERIFIER_nondet_bool();
    _x__J118 = __VERIFIER_nondet_bool();
    _x__EL_X_98 = __VERIFIER_nondet_bool();
    _x__EL_X_89 = __VERIFIER_nondet_bool();
    _x_x_2 = __VERIFIER_nondet_float();
    _x__EL_U_95 = __VERIFIER_nondet_bool();
    _x__EL_U_97 = __VERIFIER_nondet_bool();
    _x_x_1 = __VERIFIER_nondet_float();
    _x_x_0 = __VERIFIER_nondet_float();

    __ok = ((((((((x_2 + (-1.0 * _x_x_0)) <= -14.0) && ((x_3 + (-1.0 * _x_x_0)) <= -7.0)) && (((x_2 + (-1.0 * _x_x_0)) == -14.0) || ((x_3 + (-1.0 * _x_x_0)) == -7.0))) && ((((x_0 + (-1.0 * _x_x_1)) <= -17.0) && ((x_1 + (-1.0 * _x_x_1)) <= -7.0)) && (((x_0 + (-1.0 * _x_x_1)) == -17.0) || ((x_1 + (-1.0 * _x_x_1)) == -7.0)))) && ((((x_2 + (-1.0 * _x_x_2)) <= -5.0) && ((x_3 + (-1.0 * _x_x_2)) <= -6.0)) && (((x_2 + (-1.0 * _x_x_2)) == -5.0) || ((x_3 + (-1.0 * _x_x_2)) == -6.0)))) && ((((x_1 + (-1.0 * _x_x_3)) <= -8.0) && ((x_2 + (-1.0 * _x_x_3)) <= -10.0)) && (((x_1 + (-1.0 * _x_x_3)) == -8.0) || ((x_2 + (-1.0 * _x_x_3)) == -10.0)))) && ((((_EL_X_98 == (_x__EL_U_97 || ( !(_x__EL_U_95 || ( !_x__EL_X_89))))) && ((_EL_U_97 == (_x__EL_U_97 || ( !(_x__EL_U_95 || ( !_x__EL_X_89))))) && ((_EL_X_89 == ((_x_x_1 + (-1.0 * _x_x_2)) <= -4.0)) && (_EL_U_95 == (_x__EL_U_95 || ( !_x__EL_X_89)))))) && (_x__J118 == (( !(_J118 && _J124)) && ((_J118 && _J124) || ((( !_EL_X_89) || ( !(_EL_U_95 || ( !_EL_X_89)))) || _J118))))) && (_x__J124 == (( !(_J118 && _J124)) && ((_J118 && _J124) || ((( !(_EL_U_95 || ( !_EL_X_89))) || ( !(_EL_U_97 || ( !(_EL_U_95 || ( !_EL_X_89)))))) || _J124))))));
    x_3 = _x_x_3;
    _J124 = _x__J124;
    _J118 = _x__J118;
    _EL_X_98 = _x__EL_X_98;
    _EL_X_89 = _x__EL_X_89;
    x_2 = _x_x_2;
    _EL_U_95 = _x__EL_U_95;
    _EL_U_97 = _x__EL_U_97;
    x_1 = _x_x_1;
    x_0 = _x_x_0;

  }
}
