extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);
typedef enum {false, true} bool;
bool __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}

int main()
{
bool _J122, _x__J122;
float x_2, _x_x_2;
bool _J112, _x__J112;
bool _EL_U_94, _x__EL_U_94;
float x_3, _x_x_3;
float x_1, _x_x_1;
float x_0, _x_x_0;
bool _EL_U_97, _x__EL_U_97;

  int __steps_to_fair = __VERIFIER_nondet_int();
  _J122 = __VERIFIER_nondet_bool();
  x_2 = __VERIFIER_nondet_float();
  _J112 = __VERIFIER_nondet_bool();
  _EL_U_94 = __VERIFIER_nondet_bool();
  x_3 = __VERIFIER_nondet_float();
  x_1 = __VERIFIER_nondet_float();
  x_0 = __VERIFIER_nondet_float();
  _EL_U_97 = __VERIFIER_nondet_bool();

  bool __ok = (1 && ((( !(_EL_U_97 || ((-5.0 <= (x_0 + (-1.0 * x_3))) && ( !(( !((x_1 + (-1.0 * x_3)) <= 7.0)) || _EL_U_94))))) && ( !_J112)) && ( !_J122)));
  while (__steps_to_fair >= 0 && __ok) {
    if ((_J112 && _J122)) {
      __steps_to_fair = __VERIFIER_nondet_int();
    } else {
      __steps_to_fair--;
    }
    _x__J122 = __VERIFIER_nondet_bool();
    _x_x_2 = __VERIFIER_nondet_float();
    _x__J112 = __VERIFIER_nondet_bool();
    _x__EL_U_94 = __VERIFIER_nondet_bool();
    _x_x_3 = __VERIFIER_nondet_float();
    _x_x_1 = __VERIFIER_nondet_float();
    _x_x_0 = __VERIFIER_nondet_float();
    _x__EL_U_97 = __VERIFIER_nondet_bool();

    __ok = ((((((((x_0 + (-1.0 * _x_x_0)) <= -2.0) && ((x_2 + (-1.0 * _x_x_0)) <= -1.0)) && (((x_0 + (-1.0 * _x_x_0)) == -2.0) || ((x_2 + (-1.0 * _x_x_0)) == -1.0))) && ((((x_1 + (-1.0 * _x_x_1)) <= -19.0) && ((x_3 + (-1.0 * _x_x_1)) <= -12.0)) && (((x_1 + (-1.0 * _x_x_1)) == -19.0) || ((x_3 + (-1.0 * _x_x_1)) == -12.0)))) && ((((x_0 + (-1.0 * _x_x_2)) <= -14.0) && ((x_1 + (-1.0 * _x_x_2)) <= -17.0)) && (((x_0 + (-1.0 * _x_x_2)) == -14.0) || ((x_1 + (-1.0 * _x_x_2)) == -17.0)))) && ((((x_1 + (-1.0 * _x_x_3)) <= -2.0) && ((x_2 + (-1.0 * _x_x_3)) <= -17.0)) && (((x_1 + (-1.0 * _x_x_3)) == -2.0) || ((x_2 + (-1.0 * _x_x_3)) == -17.0)))) && ((((_EL_U_94 == (_x__EL_U_94 || ( !((_x_x_1 + (-1.0 * _x_x_3)) <= 7.0)))) && (_EL_U_97 == (_x__EL_U_97 || (( !(_x__EL_U_94 || ( !((_x_x_1 + (-1.0 * _x_x_3)) <= 7.0)))) && (-5.0 <= (_x_x_0 + (-1.0 * _x_x_3))))))) && (_x__J112 == (( !(_J112 && _J122)) && ((_J112 && _J122) || ((( !((x_1 + (-1.0 * x_3)) <= 7.0)) || ( !(( !((x_1 + (-1.0 * x_3)) <= 7.0)) || _EL_U_94))) || _J112))))) && (_x__J122 == (( !(_J112 && _J122)) && ((_J112 && _J122) || ((((-5.0 <= (x_0 + (-1.0 * x_3))) && ( !(( !((x_1 + (-1.0 * x_3)) <= 7.0)) || _EL_U_94))) || ( !(_EL_U_97 || ((-5.0 <= (x_0 + (-1.0 * x_3))) && ( !(( !((x_1 + (-1.0 * x_3)) <= 7.0)) || _EL_U_94)))))) || _J122))))));
    _J122 = _x__J122;
    x_2 = _x_x_2;
    _J112 = _x__J112;
    _EL_U_94 = _x__EL_U_94;
    x_3 = _x_x_3;
    x_1 = _x_x_1;
    x_0 = _x_x_0;
    _EL_U_97 = _x__EL_U_97;

  }
}
