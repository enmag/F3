extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);
typedef enum {false, true} bool;
bool __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}

int main()
{
bool _J131, _x__J131;
float x_1, _x_x_1;
bool _J120, _x__J120;
bool _EL_U_102, _x__EL_U_102;
bool _EL_X_90, _x__EL_X_90;
bool _EL_U_104, _x__EL_U_104;
float x_2, _x_x_2;
float x_0, _x_x_0;
float x_3, _x_x_3;

  int __steps_to_fair = __VERIFIER_nondet_int();
  _J131 = __VERIFIER_nondet_bool();
  x_1 = __VERIFIER_nondet_float();
  _J120 = __VERIFIER_nondet_bool();
  _EL_U_102 = __VERIFIER_nondet_bool();
  _EL_X_90 = __VERIFIER_nondet_bool();
  _EL_U_104 = __VERIFIER_nondet_bool();
  x_2 = __VERIFIER_nondet_float();
  x_0 = __VERIFIER_nondet_float();
  x_3 = __VERIFIER_nondet_float();

  bool __ok = (1 && (((( !((x_0 + (-1.0 * x_2)) <= 20.0)) || (_EL_U_104 && ( !(_EL_X_90 || _EL_U_102)))) && ( !_J120)) && ( !_J131)));
  while (__steps_to_fair >= 0 && __ok) {
    if ((_J120 && _J131)) {
      __steps_to_fair = __VERIFIER_nondet_int();
    } else {
      __steps_to_fair--;
    }
    _x__J131 = __VERIFIER_nondet_bool();
    _x_x_1 = __VERIFIER_nondet_float();
    _x__J120 = __VERIFIER_nondet_bool();
    _x__EL_U_102 = __VERIFIER_nondet_bool();
    _x__EL_X_90 = __VERIFIER_nondet_bool();
    _x__EL_U_104 = __VERIFIER_nondet_bool();
    _x_x_2 = __VERIFIER_nondet_float();
    _x_x_0 = __VERIFIER_nondet_float();
    _x_x_3 = __VERIFIER_nondet_float();

    __ok = ((((((((x_1 + (-1.0 * _x_x_0)) <= -8.0) && ((x_3 + (-1.0 * _x_x_0)) <= -18.0)) && (((x_1 + (-1.0 * _x_x_0)) == -8.0) || ((x_3 + (-1.0 * _x_x_0)) == -18.0))) && ((((x_0 + (-1.0 * _x_x_1)) <= -11.0) && ((x_2 + (-1.0 * _x_x_1)) <= -9.0)) && (((x_0 + (-1.0 * _x_x_1)) == -11.0) || ((x_2 + (-1.0 * _x_x_1)) == -9.0)))) && ((((x_2 + (-1.0 * _x_x_2)) <= -2.0) && ((x_3 + (-1.0 * _x_x_2)) <= -1.0)) && (((x_2 + (-1.0 * _x_x_2)) == -2.0) || ((x_3 + (-1.0 * _x_x_2)) == -1.0)))) && ((((x_1 + (-1.0 * _x_x_3)) <= -17.0) && ((x_3 + (-1.0 * _x_x_3)) <= -12.0)) && (((x_1 + (-1.0 * _x_x_3)) == -17.0) || ((x_3 + (-1.0 * _x_x_3)) == -12.0)))) && ((((_EL_U_104 == ((_x__EL_U_104 && ( !(_x__EL_U_102 || _x__EL_X_90))) || ( !((_x_x_0 + (-1.0 * _x_x_2)) <= 20.0)))) && ((_EL_X_90 == ((_x_x_0 + (-1.0 * _x_x_3)) <= 14.0)) && (_EL_U_102 == (_x__EL_U_102 || _x__EL_X_90)))) && (_x__J120 == (( !(_J120 && _J131)) && ((_J120 && _J131) || ((_EL_X_90 || ( !(_EL_X_90 || _EL_U_102))) || _J120))))) && (_x__J131 == (( !(_J120 && _J131)) && ((_J120 && _J131) || ((( !((x_0 + (-1.0 * x_2)) <= 20.0)) || ( !(( !((x_0 + (-1.0 * x_2)) <= 20.0)) || (_EL_U_104 && ( !(_EL_X_90 || _EL_U_102)))))) || _J131))))));
    _J131 = _x__J131;
    x_1 = _x_x_1;
    _J120 = _x__J120;
    _EL_U_102 = _x__EL_U_102;
    _EL_X_90 = _x__EL_X_90;
    _EL_U_104 = _x__EL_U_104;
    x_2 = _x_x_2;
    x_0 = _x_x_0;
    x_3 = _x_x_3;

  }
}
