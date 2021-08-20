extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);
typedef enum {false, true} bool;
bool __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}

int main()
{
bool _J119, _x__J119;
bool _J112, _x__J112;
bool _EL_U_93, _x__EL_U_93;
float x_3, _x_x_3;
float x_2, _x_x_2;
bool _EL_U_95, _x__EL_U_95;
float x_1, _x_x_1;
float x_0, _x_x_0;

  int __steps_to_fair = __VERIFIER_nondet_int();
  _J119 = __VERIFIER_nondet_bool();
  _J112 = __VERIFIER_nondet_bool();
  _EL_U_93 = __VERIFIER_nondet_bool();
  x_3 = __VERIFIER_nondet_float();
  x_2 = __VERIFIER_nondet_float();
  _EL_U_95 = __VERIFIER_nondet_bool();
  x_1 = __VERIFIER_nondet_float();
  x_0 = __VERIFIER_nondet_float();

  bool __ok = (1 && ((( !(( !(( !((x_0 + (-1.0 * x_2)) <= -20.0)) || _EL_U_95)) && ((11.0 <= (x_2 + (-1.0 * x_3))) || _EL_U_93))) && ( !_J112)) && ( !_J119)));
  while (__steps_to_fair >= 0 && __ok) {
    if ((_J112 && _J119)) {
      __steps_to_fair = __VERIFIER_nondet_int();
    } else {
      __steps_to_fair--;
    }
    _x__J119 = __VERIFIER_nondet_bool();
    _x__J112 = __VERIFIER_nondet_bool();
    _x__EL_U_93 = __VERIFIER_nondet_bool();
    _x_x_3 = __VERIFIER_nondet_float();
    _x_x_2 = __VERIFIER_nondet_float();
    _x__EL_U_95 = __VERIFIER_nondet_bool();
    _x_x_1 = __VERIFIER_nondet_float();
    _x_x_0 = __VERIFIER_nondet_float();

    __ok = ((((((((x_1 + (-1.0 * _x_x_0)) <= -19.0) && ((x_2 + (-1.0 * _x_x_0)) <= -6.0)) && (((x_1 + (-1.0 * _x_x_0)) == -19.0) || ((x_2 + (-1.0 * _x_x_0)) == -6.0))) && ((((x_1 + (-1.0 * _x_x_1)) <= -4.0) && ((x_3 + (-1.0 * _x_x_1)) <= -6.0)) && (((x_1 + (-1.0 * _x_x_1)) == -4.0) || ((x_3 + (-1.0 * _x_x_1)) == -6.0)))) && ((((x_1 + (-1.0 * _x_x_2)) <= -9.0) && ((x_3 + (-1.0 * _x_x_2)) <= -20.0)) && (((x_1 + (-1.0 * _x_x_2)) == -9.0) || ((x_3 + (-1.0 * _x_x_2)) == -20.0)))) && ((((x_0 + (-1.0 * _x_x_3)) <= -17.0) && ((x_2 + (-1.0 * _x_x_3)) <= -17.0)) && (((x_0 + (-1.0 * _x_x_3)) == -17.0) || ((x_2 + (-1.0 * _x_x_3)) == -17.0)))) && ((((_EL_U_95 == (_x__EL_U_95 || ( !((_x_x_0 + (-1.0 * _x_x_2)) <= -20.0)))) && (_EL_U_93 == (_x__EL_U_93 || (11.0 <= (_x_x_2 + (-1.0 * _x_x_3)))))) && (_x__J112 == (( !(_J112 && _J119)) && ((_J112 && _J119) || ((( !((x_0 + (-1.0 * x_2)) <= -20.0)) || ( !(( !((x_0 + (-1.0 * x_2)) <= -20.0)) || _EL_U_95))) || _J112))))) && (_x__J119 == (( !(_J112 && _J119)) && ((_J112 && _J119) || (((11.0 <= (x_2 + (-1.0 * x_3))) || ( !((11.0 <= (x_2 + (-1.0 * x_3))) || _EL_U_93))) || _J119))))));
    _J119 = _x__J119;
    _J112 = _x__J112;
    _EL_U_93 = _x__EL_U_93;
    x_3 = _x_x_3;
    x_2 = _x_x_2;
    _EL_U_95 = _x__EL_U_95;
    x_1 = _x_x_1;
    x_0 = _x_x_0;

  }
}
