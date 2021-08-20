extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);
typedef enum {false, true} bool;
bool __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}

int main()
{
bool _J117, _x__J117;
bool _J108, _x__J108;
bool _EL_U_91, _x__EL_U_91;
float x_2, _x_x_2;
float x_0, _x_x_0;
float x_1, _x_x_1;
bool _EL_U_94, _x__EL_U_94;
float x_3, _x_x_3;

  int __steps_to_fair = __VERIFIER_nondet_int();
  _J117 = __VERIFIER_nondet_bool();
  _J108 = __VERIFIER_nondet_bool();
  _EL_U_91 = __VERIFIER_nondet_bool();
  x_2 = __VERIFIER_nondet_float();
  x_0 = __VERIFIER_nondet_float();
  x_1 = __VERIFIER_nondet_float();
  _EL_U_94 = __VERIFIER_nondet_bool();
  x_3 = __VERIFIER_nondet_float();

  bool __ok = (1 && ((( !(_EL_U_94 || (( !((x_0 + (-1.0 * x_2)) <= -3.0)) || ( !(((x_0 + (-1.0 * x_2)) <= -3.0) || _EL_U_91))))) && ( !_J108)) && ( !_J117)));
  while (__steps_to_fair >= 0 && __ok) {
    if ((_J108 && _J117)) {
      __steps_to_fair = __VERIFIER_nondet_int();
    } else {
      __steps_to_fair--;
    }
    _x__J117 = __VERIFIER_nondet_bool();
    _x__J108 = __VERIFIER_nondet_bool();
    _x__EL_U_91 = __VERIFIER_nondet_bool();
    _x_x_2 = __VERIFIER_nondet_float();
    _x_x_0 = __VERIFIER_nondet_float();
    _x_x_1 = __VERIFIER_nondet_float();
    _x__EL_U_94 = __VERIFIER_nondet_bool();
    _x_x_3 = __VERIFIER_nondet_float();

    __ok = ((((((((x_2 + (-1.0 * _x_x_0)) <= -4.0) && ((x_3 + (-1.0 * _x_x_0)) <= -5.0)) && (((x_2 + (-1.0 * _x_x_0)) == -4.0) || ((x_3 + (-1.0 * _x_x_0)) == -5.0))) && ((((x_2 + (-1.0 * _x_x_1)) <= -11.0) && ((x_3 + (-1.0 * _x_x_1)) <= -18.0)) && (((x_2 + (-1.0 * _x_x_1)) == -11.0) || ((x_3 + (-1.0 * _x_x_1)) == -18.0)))) && ((((x_1 + (-1.0 * _x_x_2)) <= -7.0) && ((x_3 + (-1.0 * _x_x_2)) <= -8.0)) && (((x_1 + (-1.0 * _x_x_2)) == -7.0) || ((x_3 + (-1.0 * _x_x_2)) == -8.0)))) && ((((x_0 + (-1.0 * _x_x_3)) <= -11.0) && ((x_3 + (-1.0 * _x_x_3)) <= -20.0)) && (((x_0 + (-1.0 * _x_x_3)) == -11.0) || ((x_3 + (-1.0 * _x_x_3)) == -20.0)))) && ((((_EL_U_91 == (_x__EL_U_91 || ((_x_x_0 + (-1.0 * _x_x_2)) <= -3.0))) && (_EL_U_94 == (_x__EL_U_94 || (( !(_x__EL_U_91 || ((_x_x_0 + (-1.0 * _x_x_2)) <= -3.0))) || ( !((_x_x_0 + (-1.0 * _x_x_2)) <= -3.0)))))) && (_x__J108 == (( !(_J108 && _J117)) && ((_J108 && _J117) || ((((x_0 + (-1.0 * x_2)) <= -3.0) || ( !(((x_0 + (-1.0 * x_2)) <= -3.0) || _EL_U_91))) || _J108))))) && (_x__J117 == (( !(_J108 && _J117)) && ((_J108 && _J117) || (((( !((x_0 + (-1.0 * x_2)) <= -3.0)) || ( !(((x_0 + (-1.0 * x_2)) <= -3.0) || _EL_U_91))) || ( !(_EL_U_94 || (( !((x_0 + (-1.0 * x_2)) <= -3.0)) || ( !(((x_0 + (-1.0 * x_2)) <= -3.0) || _EL_U_91)))))) || _J117))))));
    _J117 = _x__J117;
    _J108 = _x__J108;
    _EL_U_91 = _x__EL_U_91;
    x_2 = _x_x_2;
    x_0 = _x_x_0;
    x_1 = _x_x_1;
    _EL_U_94 = _x__EL_U_94;
    x_3 = _x_x_3;

  }
}
