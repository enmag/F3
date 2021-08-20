extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);
typedef enum {false, true} bool;
bool __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}

int main()
{
bool _J123, _x__J123;
bool _J117, _x__J117;
bool _EL_U_96, _x__EL_U_96;
float x_2, _x_x_2;
float x_1, _x_x_1;
float x_3, _x_x_3;
float x_0, _x_x_0;
bool _EL_U_98, _x__EL_U_98;

  int __steps_to_fair = __VERIFIER_nondet_int();
  _J123 = __VERIFIER_nondet_bool();
  _J117 = __VERIFIER_nondet_bool();
  _EL_U_96 = __VERIFIER_nondet_bool();
  x_2 = __VERIFIER_nondet_float();
  x_1 = __VERIFIER_nondet_float();
  x_3 = __VERIFIER_nondet_float();
  x_0 = __VERIFIER_nondet_float();
  _EL_U_98 = __VERIFIER_nondet_bool();

  bool __ok = (1 && ((( !(_EL_U_98 || ( !(( !(( !((x_0 + (-1.0 * x_3)) <= 16.0)) && (-7.0 <= (x_1 + (-1.0 * x_2))))) || _EL_U_96)))) && ( !_J117)) && ( !_J123)));
  while (__steps_to_fair >= 0 && __ok) {
    if ((_J117 && _J123)) {
      __steps_to_fair = __VERIFIER_nondet_int();
    } else {
      __steps_to_fair--;
    }
    _x__J123 = __VERIFIER_nondet_bool();
    _x__J117 = __VERIFIER_nondet_bool();
    _x__EL_U_96 = __VERIFIER_nondet_bool();
    _x_x_2 = __VERIFIER_nondet_float();
    _x_x_1 = __VERIFIER_nondet_float();
    _x_x_3 = __VERIFIER_nondet_float();
    _x_x_0 = __VERIFIER_nondet_float();
    _x__EL_U_98 = __VERIFIER_nondet_bool();

    __ok = ((((((((x_2 + (-1.0 * _x_x_0)) <= -3.0) && ((x_3 + (-1.0 * _x_x_0)) <= -2.0)) && (((x_2 + (-1.0 * _x_x_0)) == -3.0) || ((x_3 + (-1.0 * _x_x_0)) == -2.0))) && ((((x_1 + (-1.0 * _x_x_1)) <= -10.0) && ((x_3 + (-1.0 * _x_x_1)) <= -6.0)) && (((x_1 + (-1.0 * _x_x_1)) == -10.0) || ((x_3 + (-1.0 * _x_x_1)) == -6.0)))) && ((((x_0 + (-1.0 * _x_x_2)) <= -5.0) && ((x_2 + (-1.0 * _x_x_2)) <= -15.0)) && (((x_0 + (-1.0 * _x_x_2)) == -5.0) || ((x_2 + (-1.0 * _x_x_2)) == -15.0)))) && ((((x_0 + (-1.0 * _x_x_3)) <= -11.0) && ((x_1 + (-1.0 * _x_x_3)) <= -15.0)) && (((x_0 + (-1.0 * _x_x_3)) == -11.0) || ((x_1 + (-1.0 * _x_x_3)) == -15.0)))) && ((((_EL_U_96 == (_x__EL_U_96 || ( !((-7.0 <= (_x_x_1 + (-1.0 * _x_x_2))) && ( !((_x_x_0 + (-1.0 * _x_x_3)) <= 16.0)))))) && (_EL_U_98 == (_x__EL_U_98 || ( !(_x__EL_U_96 || ( !((-7.0 <= (_x_x_1 + (-1.0 * _x_x_2))) && ( !((_x_x_0 + (-1.0 * _x_x_3)) <= 16.0))))))))) && (_x__J117 == (( !(_J117 && _J123)) && ((_J117 && _J123) || ((( !(( !((x_0 + (-1.0 * x_3)) <= 16.0)) && (-7.0 <= (x_1 + (-1.0 * x_2))))) || ( !(( !(( !((x_0 + (-1.0 * x_3)) <= 16.0)) && (-7.0 <= (x_1 + (-1.0 * x_2))))) || _EL_U_96))) || _J117))))) && (_x__J123 == (( !(_J117 && _J123)) && ((_J117 && _J123) || ((( !(( !(( !((x_0 + (-1.0 * x_3)) <= 16.0)) && (-7.0 <= (x_1 + (-1.0 * x_2))))) || _EL_U_96)) || ( !(_EL_U_98 || ( !(( !(( !((x_0 + (-1.0 * x_3)) <= 16.0)) && (-7.0 <= (x_1 + (-1.0 * x_2))))) || _EL_U_96))))) || _J123))))));
    _J123 = _x__J123;
    _J117 = _x__J117;
    _EL_U_96 = _x__EL_U_96;
    x_2 = _x_x_2;
    x_1 = _x_x_1;
    x_3 = _x_x_3;
    x_0 = _x_x_0;
    _EL_U_98 = _x__EL_U_98;

  }
}
