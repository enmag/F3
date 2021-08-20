extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);
typedef enum {false, true} bool;
bool __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}

int main()
{
float x_1, _x_x_1;
bool _J125, _x__J125;
bool _J119, _x__J119;
bool _EL_U_99, _x__EL_U_99;
bool _EL_X_95, _x__EL_X_95;
float x_0, _x_x_0;
float x_3, _x_x_3;
bool _EL_U_93, _x__EL_U_93;
float x_2, _x_x_2;

  int __steps_to_fair = __VERIFIER_nondet_int();
  x_1 = __VERIFIER_nondet_float();
  _J125 = __VERIFIER_nondet_bool();
  _J119 = __VERIFIER_nondet_bool();
  _EL_U_99 = __VERIFIER_nondet_bool();
  _EL_X_95 = __VERIFIER_nondet_bool();
  x_0 = __VERIFIER_nondet_float();
  x_3 = __VERIFIER_nondet_float();
  _EL_U_93 = __VERIFIER_nondet_bool();
  x_2 = __VERIFIER_nondet_float();

  bool __ok = (1 && (((_EL_X_95 || _EL_U_99) && ( !_J119)) && ( !_J125)));
  while (__steps_to_fair >= 0 && __ok) {
    if ((_J119 && _J125)) {
      __steps_to_fair = __VERIFIER_nondet_int();
    } else {
      __steps_to_fair--;
    }
    _x_x_1 = __VERIFIER_nondet_float();
    _x__J125 = __VERIFIER_nondet_bool();
    _x__J119 = __VERIFIER_nondet_bool();
    _x__EL_U_99 = __VERIFIER_nondet_bool();
    _x__EL_X_95 = __VERIFIER_nondet_bool();
    _x_x_0 = __VERIFIER_nondet_float();
    _x_x_3 = __VERIFIER_nondet_float();
    _x__EL_U_93 = __VERIFIER_nondet_bool();
    _x_x_2 = __VERIFIER_nondet_float();

    __ok = ((((((((x_1 + (-1.0 * _x_x_0)) <= -10.0) && ((x_3 + (-1.0 * _x_x_0)) <= -12.0)) && (((x_1 + (-1.0 * _x_x_0)) == -10.0) || ((x_3 + (-1.0 * _x_x_0)) == -12.0))) && ((((x_0 + (-1.0 * _x_x_1)) <= -4.0) && ((x_2 + (-1.0 * _x_x_1)) <= -18.0)) && (((x_0 + (-1.0 * _x_x_1)) == -4.0) || ((x_2 + (-1.0 * _x_x_1)) == -18.0)))) && ((((x_0 + (-1.0 * _x_x_2)) <= -14.0) && ((x_3 + (-1.0 * _x_x_2)) <= -19.0)) && (((x_0 + (-1.0 * _x_x_2)) == -14.0) || ((x_3 + (-1.0 * _x_x_2)) == -19.0)))) && ((((x_2 + (-1.0 * _x_x_3)) <= -4.0) && ((x_3 + (-1.0 * _x_x_3)) <= -18.0)) && (((x_2 + (-1.0 * _x_x_3)) == -4.0) || ((x_3 + (-1.0 * _x_x_3)) == -18.0)))) && ((((_EL_U_99 == (_x__EL_U_99 || _x__EL_X_95)) && ((_EL_U_93 == ((_x__EL_U_93 && ( !((_x_x_0 + (-1.0 * _x_x_2)) <= 3.0))) || ((_x_x_0 + (-1.0 * _x_x_1)) <= -17.0))) && (_EL_X_95 == ((_x__EL_U_93 && ( !((_x_x_0 + (-1.0 * _x_x_2)) <= 3.0))) || ((_x_x_0 + (-1.0 * _x_x_1)) <= -17.0))))) && (_x__J119 == (( !(_J119 && _J125)) && ((_J119 && _J125) || ((((x_0 + (-1.0 * x_1)) <= -17.0) || ( !(((x_0 + (-1.0 * x_1)) <= -17.0) || (( !((x_0 + (-1.0 * x_2)) <= 3.0)) && _EL_U_93)))) || _J119))))) && (_x__J125 == (( !(_J119 && _J125)) && ((_J119 && _J125) || ((_EL_X_95 || ( !(_EL_X_95 || _EL_U_99))) || _J125))))));
    x_1 = _x_x_1;
    _J125 = _x__J125;
    _J119 = _x__J119;
    _EL_U_99 = _x__EL_U_99;
    _EL_X_95 = _x__EL_X_95;
    x_0 = _x_x_0;
    x_3 = _x_x_3;
    _EL_U_93 = _x__EL_U_93;
    x_2 = _x_x_2;

  }
}
