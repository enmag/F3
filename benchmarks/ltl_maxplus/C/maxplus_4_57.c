extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);
typedef enum {false, true} bool;
bool __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}

int main()
{
bool _J129, _x__J129;
float x_1, _x_x_1;
bool _J123, _x__J123;
bool _EL_X_86, _x__EL_X_86;
bool _EL_U_95, _x__EL_U_95;
float x_2, _x_x_2;
float x_0, _x_x_0;
bool _EL_U_99, _x__EL_U_99;
float x_3, _x_x_3;

  int __steps_to_fair = __VERIFIER_nondet_int();
  _J129 = __VERIFIER_nondet_bool();
  x_1 = __VERIFIER_nondet_float();
  _J123 = __VERIFIER_nondet_bool();
  _EL_X_86 = __VERIFIER_nondet_bool();
  _EL_U_95 = __VERIFIER_nondet_bool();
  x_2 = __VERIFIER_nondet_float();
  x_0 = __VERIFIER_nondet_float();
  _EL_U_99 = __VERIFIER_nondet_bool();
  x_3 = __VERIFIER_nondet_float();

  bool __ok = (1 && ((( !(_EL_U_99 || ( !(( !((x_0 + (-1.0 * x_2)) <= -13.0)) || (_EL_U_95 && ( !_EL_X_86)))))) && ( !_J123)) && ( !_J129)));
  while (__steps_to_fair >= 0 && __ok) {
    if ((_J123 && _J129)) {
      __steps_to_fair = __VERIFIER_nondet_int();
    } else {
      __steps_to_fair--;
    }
    _x__J129 = __VERIFIER_nondet_bool();
    _x_x_1 = __VERIFIER_nondet_float();
    _x__J123 = __VERIFIER_nondet_bool();
    _x__EL_X_86 = __VERIFIER_nondet_bool();
    _x__EL_U_95 = __VERIFIER_nondet_bool();
    _x_x_2 = __VERIFIER_nondet_float();
    _x_x_0 = __VERIFIER_nondet_float();
    _x__EL_U_99 = __VERIFIER_nondet_bool();
    _x_x_3 = __VERIFIER_nondet_float();

    __ok = ((((((((x_0 + (-1.0 * _x_x_0)) <= -10.0) && ((x_2 + (-1.0 * _x_x_0)) <= -8.0)) && (((x_0 + (-1.0 * _x_x_0)) == -10.0) || ((x_2 + (-1.0 * _x_x_0)) == -8.0))) && ((((x_0 + (-1.0 * _x_x_1)) <= -8.0) && ((x_1 + (-1.0 * _x_x_1)) <= -9.0)) && (((x_0 + (-1.0 * _x_x_1)) == -8.0) || ((x_1 + (-1.0 * _x_x_1)) == -9.0)))) && ((((x_0 + (-1.0 * _x_x_2)) <= -18.0) && ((x_3 + (-1.0 * _x_x_2)) <= -20.0)) && (((x_0 + (-1.0 * _x_x_2)) == -18.0) || ((x_3 + (-1.0 * _x_x_2)) == -20.0)))) && ((((x_1 + (-1.0 * _x_x_3)) <= -12.0) && ((x_3 + (-1.0 * _x_x_3)) <= -1.0)) && (((x_1 + (-1.0 * _x_x_3)) == -12.0) || ((x_3 + (-1.0 * _x_x_3)) == -1.0)))) && ((((_EL_U_99 == (_x__EL_U_99 || ( !((_x__EL_U_95 && ( !_x__EL_X_86)) || ( !((_x_x_0 + (-1.0 * _x_x_2)) <= -13.0)))))) && ((_EL_X_86 == ((_x_x_0 + (-1.0 * _x_x_1)) <= -12.0)) && (_EL_U_95 == ((_x__EL_U_95 && ( !_x__EL_X_86)) || ( !((_x_x_0 + (-1.0 * _x_x_2)) <= -13.0)))))) && (_x__J123 == (( !(_J123 && _J129)) && ((_J123 && _J129) || ((( !((x_0 + (-1.0 * x_2)) <= -13.0)) || ( !(( !((x_0 + (-1.0 * x_2)) <= -13.0)) || (_EL_U_95 && ( !_EL_X_86))))) || _J123))))) && (_x__J129 == (( !(_J123 && _J129)) && ((_J123 && _J129) || ((( !(( !((x_0 + (-1.0 * x_2)) <= -13.0)) || (_EL_U_95 && ( !_EL_X_86)))) || ( !(_EL_U_99 || ( !(( !((x_0 + (-1.0 * x_2)) <= -13.0)) || (_EL_U_95 && ( !_EL_X_86))))))) || _J129))))));
    _J129 = _x__J129;
    x_1 = _x_x_1;
    _J123 = _x__J123;
    _EL_X_86 = _x__EL_X_86;
    _EL_U_95 = _x__EL_U_95;
    x_2 = _x_x_2;
    x_0 = _x_x_0;
    _EL_U_99 = _x__EL_U_99;
    x_3 = _x_x_3;

  }
}
