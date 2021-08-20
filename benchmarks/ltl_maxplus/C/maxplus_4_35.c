extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);
typedef enum {false, true} bool;
bool __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}

int main()
{
bool _J117, _x__J117;
float x_0, _x_x_0;
bool _J110, _x__J110;
bool _EL_U_93, _x__EL_U_93;
float x_2, _x_x_2;
float x_1, _x_x_1;
float x_3, _x_x_3;
bool _EL_U_94, _x__EL_U_94;

  int __steps_to_fair = __VERIFIER_nondet_int();
  _J117 = __VERIFIER_nondet_bool();
  x_0 = __VERIFIER_nondet_float();
  _J110 = __VERIFIER_nondet_bool();
  _EL_U_93 = __VERIFIER_nondet_bool();
  x_2 = __VERIFIER_nondet_float();
  x_1 = __VERIFIER_nondet_float();
  x_3 = __VERIFIER_nondet_float();
  _EL_U_94 = __VERIFIER_nondet_bool();

  bool __ok = (1 && ((( !(( !(((x_1 + (-1.0 * x_2)) <= -9.0) || _EL_U_94)) && (( !(6.0 <= (x_1 + (-1.0 * x_2)))) || _EL_U_93))) && ( !_J110)) && ( !_J117)));
  while (__steps_to_fair >= 0 && __ok) {
    if ((_J110 && _J117)) {
      __steps_to_fair = __VERIFIER_nondet_int();
    } else {
      __steps_to_fair--;
    }
    _x__J117 = __VERIFIER_nondet_bool();
    _x_x_0 = __VERIFIER_nondet_float();
    _x__J110 = __VERIFIER_nondet_bool();
    _x__EL_U_93 = __VERIFIER_nondet_bool();
    _x_x_2 = __VERIFIER_nondet_float();
    _x_x_1 = __VERIFIER_nondet_float();
    _x_x_3 = __VERIFIER_nondet_float();
    _x__EL_U_94 = __VERIFIER_nondet_bool();

    __ok = ((((((((x_0 + (-1.0 * _x_x_0)) <= -17.0) && ((x_2 + (-1.0 * _x_x_0)) <= -17.0)) && (((x_0 + (-1.0 * _x_x_0)) == -17.0) || ((x_2 + (-1.0 * _x_x_0)) == -17.0))) && ((((x_0 + (-1.0 * _x_x_1)) <= -13.0) && ((x_3 + (-1.0 * _x_x_1)) <= -19.0)) && (((x_0 + (-1.0 * _x_x_1)) == -13.0) || ((x_3 + (-1.0 * _x_x_1)) == -19.0)))) && ((((x_2 + (-1.0 * _x_x_2)) <= -3.0) && ((x_3 + (-1.0 * _x_x_2)) <= -2.0)) && (((x_2 + (-1.0 * _x_x_2)) == -3.0) || ((x_3 + (-1.0 * _x_x_2)) == -2.0)))) && ((((x_0 + (-1.0 * _x_x_3)) <= -2.0) && ((x_1 + (-1.0 * _x_x_3)) <= -2.0)) && (((x_0 + (-1.0 * _x_x_3)) == -2.0) || ((x_1 + (-1.0 * _x_x_3)) == -2.0)))) && ((((_EL_U_94 == (_x__EL_U_94 || ((_x_x_1 + (-1.0 * _x_x_2)) <= -9.0))) && (_EL_U_93 == (_x__EL_U_93 || ( !(6.0 <= (_x_x_1 + (-1.0 * _x_x_2))))))) && (_x__J110 == (( !(_J110 && _J117)) && ((_J110 && _J117) || ((((x_1 + (-1.0 * x_2)) <= -9.0) || ( !(((x_1 + (-1.0 * x_2)) <= -9.0) || _EL_U_94))) || _J110))))) && (_x__J117 == (( !(_J110 && _J117)) && ((_J110 && _J117) || ((( !(6.0 <= (x_1 + (-1.0 * x_2)))) || ( !(( !(6.0 <= (x_1 + (-1.0 * x_2)))) || _EL_U_93))) || _J117))))));
    _J117 = _x__J117;
    x_0 = _x_x_0;
    _J110 = _x__J110;
    _EL_U_93 = _x__EL_U_93;
    x_2 = _x_x_2;
    x_1 = _x_x_1;
    x_3 = _x_x_3;
    _EL_U_94 = _x__EL_U_94;

  }
}
