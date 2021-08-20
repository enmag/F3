extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);
typedef enum {false, true} bool;
bool __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}

int main()
{
bool _J133, _x__J133;
bool _J120, _x__J120;
bool _EL_X_91, _x__EL_X_91;
bool _EL_U_105, _x__EL_U_105;
bool _EL_U_103, _x__EL_U_103;
float x_2, _x_x_2;
float x_3, _x_x_3;
float x_1, _x_x_1;
float x_0, _x_x_0;

  int __steps_to_fair = __VERIFIER_nondet_int();
  _J133 = __VERIFIER_nondet_bool();
  _J120 = __VERIFIER_nondet_bool();
  _EL_X_91 = __VERIFIER_nondet_bool();
  _EL_U_105 = __VERIFIER_nondet_bool();
  _EL_U_103 = __VERIFIER_nondet_bool();
  x_2 = __VERIFIER_nondet_float();
  x_3 = __VERIFIER_nondet_float();
  x_1 = __VERIFIER_nondet_float();
  x_0 = __VERIFIER_nondet_float();

  bool __ok = (1 && (((( !(((x_1 + (-1.0 * x_3)) <= -3.0) || _EL_U_103)) || (_EL_U_105 && ( !_EL_X_91))) && ( !_J120)) && ( !_J133)));
  while (__steps_to_fair >= 0 && __ok) {
    if ((_J120 && _J133)) {
      __steps_to_fair = __VERIFIER_nondet_int();
    } else {
      __steps_to_fair--;
    }
    _x__J133 = __VERIFIER_nondet_bool();
    _x__J120 = __VERIFIER_nondet_bool();
    _x__EL_X_91 = __VERIFIER_nondet_bool();
    _x__EL_U_105 = __VERIFIER_nondet_bool();
    _x__EL_U_103 = __VERIFIER_nondet_bool();
    _x_x_2 = __VERIFIER_nondet_float();
    _x_x_3 = __VERIFIER_nondet_float();
    _x_x_1 = __VERIFIER_nondet_float();
    _x_x_0 = __VERIFIER_nondet_float();

    __ok = ((((((((x_0 + (-1.0 * _x_x_0)) <= -14.0) && ((x_2 + (-1.0 * _x_x_0)) <= -6.0)) && (((x_0 + (-1.0 * _x_x_0)) == -14.0) || ((x_2 + (-1.0 * _x_x_0)) == -6.0))) && ((((x_0 + (-1.0 * _x_x_1)) <= -13.0) && ((x_1 + (-1.0 * _x_x_1)) <= -17.0)) && (((x_0 + (-1.0 * _x_x_1)) == -13.0) || ((x_1 + (-1.0 * _x_x_1)) == -17.0)))) && ((((x_0 + (-1.0 * _x_x_2)) <= -18.0) && ((x_3 + (-1.0 * _x_x_2)) <= -5.0)) && (((x_0 + (-1.0 * _x_x_2)) == -18.0) || ((x_3 + (-1.0 * _x_x_2)) == -5.0)))) && ((((x_1 + (-1.0 * _x_x_3)) <= -11.0) && ((x_3 + (-1.0 * _x_x_3)) <= -12.0)) && (((x_1 + (-1.0 * _x_x_3)) == -11.0) || ((x_3 + (-1.0 * _x_x_3)) == -12.0)))) && ((((_EL_U_105 == ((_x__EL_U_105 && ( !_x__EL_X_91)) || ( !(_x__EL_U_103 || ((_x_x_1 + (-1.0 * _x_x_3)) <= -3.0))))) && ((_EL_U_103 == (_x__EL_U_103 || ((_x_x_1 + (-1.0 * _x_x_3)) <= -3.0))) && (_EL_X_91 == ((_x_x_0 + (-1.0 * _x_x_3)) <= 20.0)))) && (_x__J120 == (( !(_J120 && _J133)) && ((_J120 && _J133) || ((((x_1 + (-1.0 * x_3)) <= -3.0) || ( !(((x_1 + (-1.0 * x_3)) <= -3.0) || _EL_U_103))) || _J120))))) && (_x__J133 == (( !(_J120 && _J133)) && ((_J120 && _J133) || ((( !(((x_1 + (-1.0 * x_3)) <= -3.0) || _EL_U_103)) || ( !(( !(((x_1 + (-1.0 * x_3)) <= -3.0) || _EL_U_103)) || (_EL_U_105 && ( !_EL_X_91))))) || _J133))))));
    _J133 = _x__J133;
    _J120 = _x__J120;
    _EL_X_91 = _x__EL_X_91;
    _EL_U_105 = _x__EL_U_105;
    _EL_U_103 = _x__EL_U_103;
    x_2 = _x_x_2;
    x_3 = _x_x_3;
    x_1 = _x_x_1;
    x_0 = _x_x_0;

  }
}
