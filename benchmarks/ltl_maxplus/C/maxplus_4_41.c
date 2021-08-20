extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);
typedef enum {false, true} bool;
bool __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}

int main()
{
bool _J124, _x__J124;
bool _J115, _x__J115;
float x_3, _x_x_3;
bool _EL_U_96, _x__EL_U_96;
float x_2, _x_x_2;
float x_0, _x_x_0;
bool _EL_U_95, _x__EL_U_95;
float x_1, _x_x_1;

  int __steps_to_fair = __VERIFIER_nondet_int();
  _J124 = __VERIFIER_nondet_bool();
  _J115 = __VERIFIER_nondet_bool();
  x_3 = __VERIFIER_nondet_float();
  _EL_U_96 = __VERIFIER_nondet_bool();
  x_2 = __VERIFIER_nondet_float();
  x_0 = __VERIFIER_nondet_float();
  _EL_U_95 = __VERIFIER_nondet_bool();
  x_1 = __VERIFIER_nondet_float();

  bool __ok = (1 && ((( !(((-6.0 <= (x_1 + (-1.0 * x_2))) || (( !(10.0 <= (x_0 + (-1.0 * x_2)))) && _EL_U_95)) || (( !(x_0 <= x_2)) && _EL_U_96))) && ( !_J115)) && ( !_J124)));
  while (__steps_to_fair >= 0 && __ok) {
    if ((_J115 && _J124)) {
      __steps_to_fair = __VERIFIER_nondet_int();
    } else {
      __steps_to_fair--;
    }
    _x__J124 = __VERIFIER_nondet_bool();
    _x__J115 = __VERIFIER_nondet_bool();
    _x_x_3 = __VERIFIER_nondet_float();
    _x__EL_U_96 = __VERIFIER_nondet_bool();
    _x_x_2 = __VERIFIER_nondet_float();
    _x_x_0 = __VERIFIER_nondet_float();
    _x__EL_U_95 = __VERIFIER_nondet_bool();
    _x_x_1 = __VERIFIER_nondet_float();

    __ok = ((((((((x_1 + (-1.0 * _x_x_0)) <= -12.0) && ((x_2 + (-1.0 * _x_x_0)) <= -18.0)) && (((x_1 + (-1.0 * _x_x_0)) == -12.0) || ((x_2 + (-1.0 * _x_x_0)) == -18.0))) && ((((x_0 + (-1.0 * _x_x_1)) <= -20.0) && ((x_1 + (-1.0 * _x_x_1)) <= -4.0)) && (((x_0 + (-1.0 * _x_x_1)) == -20.0) || ((x_1 + (-1.0 * _x_x_1)) == -4.0)))) && ((((x_0 + (-1.0 * _x_x_2)) <= -20.0) && ((x_3 + (-1.0 * _x_x_2)) <= -19.0)) && (((x_0 + (-1.0 * _x_x_2)) == -20.0) || ((x_3 + (-1.0 * _x_x_2)) == -19.0)))) && ((((x_0 + (-1.0 * _x_x_3)) <= -5.0) && ((x_3 + (-1.0 * _x_x_3)) <= -13.0)) && (((x_0 + (-1.0 * _x_x_3)) == -5.0) || ((x_3 + (-1.0 * _x_x_3)) == -13.0)))) && ((((_EL_U_95 == ((_x__EL_U_95 && ( !(10.0 <= (_x_x_0 + (-1.0 * _x_x_2))))) || (-6.0 <= (_x_x_1 + (-1.0 * _x_x_2))))) && (_EL_U_96 == (((_x__EL_U_95 && ( !(10.0 <= (_x_x_0 + (-1.0 * _x_x_2))))) || (-6.0 <= (_x_x_1 + (-1.0 * _x_x_2)))) || (_x__EL_U_96 && ( !(_x_x_0 <= _x_x_2)))))) && (_x__J115 == (( !(_J115 && _J124)) && ((_J115 && _J124) || (((-6.0 <= (x_1 + (-1.0 * x_2))) || ( !((-6.0 <= (x_1 + (-1.0 * x_2))) || (( !(10.0 <= (x_0 + (-1.0 * x_2)))) && _EL_U_95)))) || _J115))))) && (_x__J124 == (( !(_J115 && _J124)) && ((_J115 && _J124) || ((((-6.0 <= (x_1 + (-1.0 * x_2))) || (( !(10.0 <= (x_0 + (-1.0 * x_2)))) && _EL_U_95)) || ( !(((-6.0 <= (x_1 + (-1.0 * x_2))) || (( !(10.0 <= (x_0 + (-1.0 * x_2)))) && _EL_U_95)) || (( !(x_0 <= x_2)) && _EL_U_96)))) || _J124))))));
    _J124 = _x__J124;
    _J115 = _x__J115;
    x_3 = _x_x_3;
    _EL_U_96 = _x__EL_U_96;
    x_2 = _x_x_2;
    x_0 = _x_x_0;
    _EL_U_95 = _x__EL_U_95;
    x_1 = _x_x_1;

  }
}
