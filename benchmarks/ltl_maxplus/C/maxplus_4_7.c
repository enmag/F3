extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);
typedef enum {false, true} bool;
bool __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}

int main()
{
bool _J125, _x__J125;
bool _J116, _x__J116;
bool _EL_U_97, _x__EL_U_97;
float x_2, _x_x_2;
float x_0, _x_x_0;
bool _EL_U_95, _x__EL_U_95;
float x_3, _x_x_3;
float x_1, _x_x_1;

  int __steps_to_fair = __VERIFIER_nondet_int();
  _J125 = __VERIFIER_nondet_bool();
  _J116 = __VERIFIER_nondet_bool();
  _EL_U_97 = __VERIFIER_nondet_bool();
  x_2 = __VERIFIER_nondet_float();
  x_0 = __VERIFIER_nondet_float();
  _EL_U_95 = __VERIFIER_nondet_bool();
  x_3 = __VERIFIER_nondet_float();
  x_1 = __VERIFIER_nondet_float();

  bool __ok = (1 && ((((((x_0 + (-1.0 * x_1)) <= -15.0) || (( !((x_0 + (-1.0 * x_2)) <= 20.0)) && _EL_U_95)) || (( !((x_0 + (-1.0 * x_2)) <= -3.0)) && _EL_U_97)) && ( !_J116)) && ( !_J125)));
  while (__steps_to_fair >= 0 && __ok) {
    if ((_J116 && _J125)) {
      __steps_to_fair = __VERIFIER_nondet_int();
    } else {
      __steps_to_fair--;
    }
    _x__J125 = __VERIFIER_nondet_bool();
    _x__J116 = __VERIFIER_nondet_bool();
    _x__EL_U_97 = __VERIFIER_nondet_bool();
    _x_x_2 = __VERIFIER_nondet_float();
    _x_x_0 = __VERIFIER_nondet_float();
    _x__EL_U_95 = __VERIFIER_nondet_bool();
    _x_x_3 = __VERIFIER_nondet_float();
    _x_x_1 = __VERIFIER_nondet_float();

    __ok = ((((((((x_0 + (-1.0 * _x_x_0)) <= -1.0) && ((x_2 + (-1.0 * _x_x_0)) <= -8.0)) && (((x_0 + (-1.0 * _x_x_0)) == -1.0) || ((x_2 + (-1.0 * _x_x_0)) == -8.0))) && ((((x_0 + (-1.0 * _x_x_1)) <= -8.0) && ((x_3 + (-1.0 * _x_x_1)) <= -9.0)) && (((x_0 + (-1.0 * _x_x_1)) == -8.0) || ((x_3 + (-1.0 * _x_x_1)) == -9.0)))) && ((((x_0 + (-1.0 * _x_x_2)) <= -15.0) && ((x_3 + (-1.0 * _x_x_2)) <= -4.0)) && (((x_0 + (-1.0 * _x_x_2)) == -15.0) || ((x_3 + (-1.0 * _x_x_2)) == -4.0)))) && ((((x_1 + (-1.0 * _x_x_3)) <= -1.0) && ((x_2 + (-1.0 * _x_x_3)) <= -11.0)) && (((x_1 + (-1.0 * _x_x_3)) == -1.0) || ((x_2 + (-1.0 * _x_x_3)) == -11.0)))) && ((((_EL_U_95 == ((_x__EL_U_95 && ( !((_x_x_0 + (-1.0 * _x_x_2)) <= 20.0))) || ((_x_x_0 + (-1.0 * _x_x_1)) <= -15.0))) && (_EL_U_97 == (((_x__EL_U_95 && ( !((_x_x_0 + (-1.0 * _x_x_2)) <= 20.0))) || ((_x_x_0 + (-1.0 * _x_x_1)) <= -15.0)) || (_x__EL_U_97 && ( !((_x_x_0 + (-1.0 * _x_x_2)) <= -3.0)))))) && (_x__J116 == (( !(_J116 && _J125)) && ((_J116 && _J125) || ((((x_0 + (-1.0 * x_1)) <= -15.0) || ( !(((x_0 + (-1.0 * x_1)) <= -15.0) || (( !((x_0 + (-1.0 * x_2)) <= 20.0)) && _EL_U_95)))) || _J116))))) && (_x__J125 == (( !(_J116 && _J125)) && ((_J116 && _J125) || (((((x_0 + (-1.0 * x_1)) <= -15.0) || (( !((x_0 + (-1.0 * x_2)) <= 20.0)) && _EL_U_95)) || ( !((((x_0 + (-1.0 * x_1)) <= -15.0) || (( !((x_0 + (-1.0 * x_2)) <= 20.0)) && _EL_U_95)) || (( !((x_0 + (-1.0 * x_2)) <= -3.0)) && _EL_U_97)))) || _J125))))));
    _J125 = _x__J125;
    _J116 = _x__J116;
    _EL_U_97 = _x__EL_U_97;
    x_2 = _x_x_2;
    x_0 = _x_x_0;
    _EL_U_95 = _x__EL_U_95;
    x_3 = _x_x_3;
    x_1 = _x_x_1;

  }
}
