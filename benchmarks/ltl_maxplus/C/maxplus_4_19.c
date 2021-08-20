extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);
typedef enum {false, true} bool;
bool __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}

int main()
{
bool _J127, _x__J127;
bool _J117, _x__J117;
bool _EL_U_92, _x__EL_U_92;
float x_3, _x_x_3;
float x_1, _x_x_1;
float x_2, _x_x_2;
bool _EL_U_98, _x__EL_U_98;
float x_0, _x_x_0;

  int __steps_to_fair = __VERIFIER_nondet_int();
  _J127 = __VERIFIER_nondet_bool();
  _J117 = __VERIFIER_nondet_bool();
  _EL_U_92 = __VERIFIER_nondet_bool();
  x_3 = __VERIFIER_nondet_float();
  x_1 = __VERIFIER_nondet_float();
  x_2 = __VERIFIER_nondet_float();
  _EL_U_98 = __VERIFIER_nondet_bool();
  x_0 = __VERIFIER_nondet_float();

  bool __ok = (1 && (((( !(-14.0 <= (x_0 + (-1.0 * x_2)))) || (_EL_U_98 && (((x_1 + (-1.0 * x_2)) <= 13.0) || (( !(-12.0 <= (x_1 + (-1.0 * x_3)))) && _EL_U_92)))) && ( !_J117)) && ( !_J127)));
  while (__steps_to_fair >= 0 && __ok) {
    if ((_J117 && _J127)) {
      __steps_to_fair = __VERIFIER_nondet_int();
    } else {
      __steps_to_fair--;
    }
    _x__J127 = __VERIFIER_nondet_bool();
    _x__J117 = __VERIFIER_nondet_bool();
    _x__EL_U_92 = __VERIFIER_nondet_bool();
    _x_x_3 = __VERIFIER_nondet_float();
    _x_x_1 = __VERIFIER_nondet_float();
    _x_x_2 = __VERIFIER_nondet_float();
    _x__EL_U_98 = __VERIFIER_nondet_bool();
    _x_x_0 = __VERIFIER_nondet_float();

    __ok = ((((((((x_1 + (-1.0 * _x_x_0)) <= -17.0) && ((x_2 + (-1.0 * _x_x_0)) <= -6.0)) && (((x_1 + (-1.0 * _x_x_0)) == -17.0) || ((x_2 + (-1.0 * _x_x_0)) == -6.0))) && ((((x_1 + (-1.0 * _x_x_1)) <= -16.0) && ((x_3 + (-1.0 * _x_x_1)) <= -19.0)) && (((x_1 + (-1.0 * _x_x_1)) == -16.0) || ((x_3 + (-1.0 * _x_x_1)) == -19.0)))) && ((((x_1 + (-1.0 * _x_x_2)) <= -4.0) && ((x_2 + (-1.0 * _x_x_2)) <= -17.0)) && (((x_1 + (-1.0 * _x_x_2)) == -4.0) || ((x_2 + (-1.0 * _x_x_2)) == -17.0)))) && ((((x_0 + (-1.0 * _x_x_3)) <= -9.0) && ((x_3 + (-1.0 * _x_x_3)) <= -5.0)) && (((x_0 + (-1.0 * _x_x_3)) == -9.0) || ((x_3 + (-1.0 * _x_x_3)) == -5.0)))) && ((((_EL_U_92 == ((_x__EL_U_92 && ( !(-12.0 <= (_x_x_1 + (-1.0 * _x_x_3))))) || ((_x_x_1 + (-1.0 * _x_x_2)) <= 13.0))) && (_EL_U_98 == ((_x__EL_U_98 && ((_x__EL_U_92 && ( !(-12.0 <= (_x_x_1 + (-1.0 * _x_x_3))))) || ((_x_x_1 + (-1.0 * _x_x_2)) <= 13.0))) || ( !(-14.0 <= (_x_x_0 + (-1.0 * _x_x_2))))))) && (_x__J117 == (( !(_J117 && _J127)) && ((_J117 && _J127) || ((((x_1 + (-1.0 * x_2)) <= 13.0) || ( !(((x_1 + (-1.0 * x_2)) <= 13.0) || (( !(-12.0 <= (x_1 + (-1.0 * x_3)))) && _EL_U_92)))) || _J117))))) && (_x__J127 == (( !(_J117 && _J127)) && ((_J117 && _J127) || ((( !(-14.0 <= (x_0 + (-1.0 * x_2)))) || ( !(( !(-14.0 <= (x_0 + (-1.0 * x_2)))) || (_EL_U_98 && (((x_1 + (-1.0 * x_2)) <= 13.0) || (( !(-12.0 <= (x_1 + (-1.0 * x_3)))) && _EL_U_92)))))) || _J127))))));
    _J127 = _x__J127;
    _J117 = _x__J117;
    _EL_U_92 = _x__EL_U_92;
    x_3 = _x_x_3;
    x_1 = _x_x_1;
    x_2 = _x_x_2;
    _EL_U_98 = _x__EL_U_98;
    x_0 = _x_x_0;

  }
}
