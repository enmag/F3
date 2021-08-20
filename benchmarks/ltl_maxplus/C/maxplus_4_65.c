extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);
typedef enum {false, true} bool;
bool __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}

int main()
{
bool _J124, _x__J124;
bool _J112, _x__J112;
bool _EL_U_93, _x__EL_U_93;
float x_2, _x_x_2;
float x_0, _x_x_0;
float x_3, _x_x_3;
float x_1, _x_x_1;
bool _EL_U_97, _x__EL_U_97;

  int __steps_to_fair = __VERIFIER_nondet_int();
  _J124 = __VERIFIER_nondet_bool();
  _J112 = __VERIFIER_nondet_bool();
  _EL_U_93 = __VERIFIER_nondet_bool();
  x_2 = __VERIFIER_nondet_float();
  x_0 = __VERIFIER_nondet_float();
  x_3 = __VERIFIER_nondet_float();
  x_1 = __VERIFIER_nondet_float();
  _EL_U_97 = __VERIFIER_nondet_bool();

  bool __ok = (1 && (((_EL_U_97 || ( !(( !(18.0 <= (x_0 + (-1.0 * x_2)))) || ( !(( !((x_0 + (-1.0 * x_2)) <= 1.0)) || _EL_U_93))))) && ( !_J112)) && ( !_J124)));
  while (__steps_to_fair >= 0 && __ok) {
    if ((_J112 && _J124)) {
      __steps_to_fair = __VERIFIER_nondet_int();
    } else {
      __steps_to_fair--;
    }
    _x__J124 = __VERIFIER_nondet_bool();
    _x__J112 = __VERIFIER_nondet_bool();
    _x__EL_U_93 = __VERIFIER_nondet_bool();
    _x_x_2 = __VERIFIER_nondet_float();
    _x_x_0 = __VERIFIER_nondet_float();
    _x_x_3 = __VERIFIER_nondet_float();
    _x_x_1 = __VERIFIER_nondet_float();
    _x__EL_U_97 = __VERIFIER_nondet_bool();

    __ok = ((((((((x_1 + (-1.0 * _x_x_0)) <= -12.0) && ((x_3 + (-1.0 * _x_x_0)) <= -20.0)) && (((x_1 + (-1.0 * _x_x_0)) == -12.0) || ((x_3 + (-1.0 * _x_x_0)) == -20.0))) && ((((x_0 + (-1.0 * _x_x_1)) <= -19.0) && ((x_2 + (-1.0 * _x_x_1)) <= -1.0)) && (((x_0 + (-1.0 * _x_x_1)) == -19.0) || ((x_2 + (-1.0 * _x_x_1)) == -1.0)))) && ((((x_0 + (-1.0 * _x_x_2)) <= -14.0) && ((x_1 + (-1.0 * _x_x_2)) <= -13.0)) && (((x_0 + (-1.0 * _x_x_2)) == -14.0) || ((x_1 + (-1.0 * _x_x_2)) == -13.0)))) && ((((x_0 + (-1.0 * _x_x_3)) <= -12.0) && ((x_2 + (-1.0 * _x_x_3)) <= -20.0)) && (((x_0 + (-1.0 * _x_x_3)) == -12.0) || ((x_2 + (-1.0 * _x_x_3)) == -20.0)))) && ((((_EL_U_93 == (_x__EL_U_93 || ( !((_x_x_0 + (-1.0 * _x_x_2)) <= 1.0)))) && (_EL_U_97 == (_x__EL_U_97 || ( !(( !(_x__EL_U_93 || ( !((_x_x_0 + (-1.0 * _x_x_2)) <= 1.0)))) || ( !(18.0 <= (_x_x_0 + (-1.0 * _x_x_2))))))))) && (_x__J112 == (( !(_J112 && _J124)) && ((_J112 && _J124) || ((( !((x_0 + (-1.0 * x_2)) <= 1.0)) || ( !(( !((x_0 + (-1.0 * x_2)) <= 1.0)) || _EL_U_93))) || _J112))))) && (_x__J124 == (( !(_J112 && _J124)) && ((_J112 && _J124) || ((( !(( !(18.0 <= (x_0 + (-1.0 * x_2)))) || ( !(( !((x_0 + (-1.0 * x_2)) <= 1.0)) || _EL_U_93)))) || ( !(_EL_U_97 || ( !(( !(18.0 <= (x_0 + (-1.0 * x_2)))) || ( !(( !((x_0 + (-1.0 * x_2)) <= 1.0)) || _EL_U_93))))))) || _J124))))));
    _J124 = _x__J124;
    _J112 = _x__J112;
    _EL_U_93 = _x__EL_U_93;
    x_2 = _x_x_2;
    x_0 = _x_x_0;
    x_3 = _x_x_3;
    x_1 = _x_x_1;
    _EL_U_97 = _x__EL_U_97;

  }
}
