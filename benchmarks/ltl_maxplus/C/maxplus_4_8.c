extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);
typedef enum {false, true} bool;
bool __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}

int main()
{
bool _J125, _x__J125;
float x_1, _x_x_1;
bool _J117, _x__J117;
bool _EL_U_95, _x__EL_U_95;
float x_3, _x_x_3;
float x_0, _x_x_0;
bool _EL_U_97, _x__EL_U_97;
bool _EL_X_91, _x__EL_X_91;
float x_2, _x_x_2;

  int __steps_to_fair = __VERIFIER_nondet_int();
  _J125 = __VERIFIER_nondet_bool();
  x_1 = __VERIFIER_nondet_float();
  _J117 = __VERIFIER_nondet_bool();
  _EL_U_95 = __VERIFIER_nondet_bool();
  x_3 = __VERIFIER_nondet_float();
  x_0 = __VERIFIER_nondet_float();
  _EL_U_97 = __VERIFIER_nondet_bool();
  _EL_X_91 = __VERIFIER_nondet_bool();
  x_2 = __VERIFIER_nondet_float();

  bool __ok = (1 && ((( !(_EL_X_91 || (_EL_U_97 && ( !(( !(5.0 <= (x_0 + (-1.0 * x_3)))) || _EL_U_95))))) && ( !_J117)) && ( !_J125)));
  while (__steps_to_fair >= 0 && __ok) {
    if ((_J117 && _J125)) {
      __steps_to_fair = __VERIFIER_nondet_int();
    } else {
      __steps_to_fair--;
    }
    _x__J125 = __VERIFIER_nondet_bool();
    _x_x_1 = __VERIFIER_nondet_float();
    _x__J117 = __VERIFIER_nondet_bool();
    _x__EL_U_95 = __VERIFIER_nondet_bool();
    _x_x_3 = __VERIFIER_nondet_float();
    _x_x_0 = __VERIFIER_nondet_float();
    _x__EL_U_97 = __VERIFIER_nondet_bool();
    _x__EL_X_91 = __VERIFIER_nondet_bool();
    _x_x_2 = __VERIFIER_nondet_float();

    __ok = ((((((((x_2 + (-1.0 * _x_x_0)) <= -7.0) && ((x_3 + (-1.0 * _x_x_0)) <= -9.0)) && (((x_2 + (-1.0 * _x_x_0)) == -7.0) || ((x_3 + (-1.0 * _x_x_0)) == -9.0))) && ((((x_2 + (-1.0 * _x_x_1)) <= -20.0) && ((x_3 + (-1.0 * _x_x_1)) <= -3.0)) && (((x_2 + (-1.0 * _x_x_1)) == -20.0) || ((x_3 + (-1.0 * _x_x_1)) == -3.0)))) && ((((x_0 + (-1.0 * _x_x_2)) <= -12.0) && ((x_1 + (-1.0 * _x_x_2)) <= -13.0)) && (((x_0 + (-1.0 * _x_x_2)) == -12.0) || ((x_1 + (-1.0 * _x_x_2)) == -13.0)))) && ((((x_1 + (-1.0 * _x_x_3)) <= -8.0) && ((x_2 + (-1.0 * _x_x_3)) <= -5.0)) && (((x_1 + (-1.0 * _x_x_3)) == -8.0) || ((x_2 + (-1.0 * _x_x_3)) == -5.0)))) && ((((_EL_U_97 == (_x__EL_X_91 || (_x__EL_U_97 && ( !(_x__EL_U_95 || ( !(5.0 <= (_x_x_0 + (-1.0 * _x_x_3))))))))) && ((_EL_X_91 == (-13.0 <= (_x_x_0 + (-1.0 * _x_x_2)))) && (_EL_U_95 == (_x__EL_U_95 || ( !(5.0 <= (_x_x_0 + (-1.0 * _x_x_3)))))))) && (_x__J117 == (( !(_J117 && _J125)) && ((_J117 && _J125) || ((( !(5.0 <= (x_0 + (-1.0 * x_3)))) || ( !(( !(5.0 <= (x_0 + (-1.0 * x_3)))) || _EL_U_95))) || _J117))))) && (_x__J125 == (( !(_J117 && _J125)) && ((_J117 && _J125) || ((_EL_X_91 || ( !(_EL_X_91 || (_EL_U_97 && ( !(( !(5.0 <= (x_0 + (-1.0 * x_3)))) || _EL_U_95)))))) || _J125))))));
    _J125 = _x__J125;
    x_1 = _x_x_1;
    _J117 = _x__J117;
    _EL_U_95 = _x__EL_U_95;
    x_3 = _x_x_3;
    x_0 = _x_x_0;
    _EL_U_97 = _x__EL_U_97;
    _EL_X_91 = _x__EL_X_91;
    x_2 = _x_x_2;

  }
}
