extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);
typedef enum {false, true} bool;
bool __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}

int main()
{
bool _J121, _x__J121;
bool _J115, _x__J115;
bool _EL_U_95, _x__EL_U_95;
float x_3, _x_x_3;
float x_0, _x_x_0;
float x_2, _x_x_2;
float x_1, _x_x_1;
bool _EL_U_97, _x__EL_U_97;

  int __steps_to_fair = __VERIFIER_nondet_int();
  _J121 = __VERIFIER_nondet_bool();
  _J115 = __VERIFIER_nondet_bool();
  _EL_U_95 = __VERIFIER_nondet_bool();
  x_3 = __VERIFIER_nondet_float();
  x_0 = __VERIFIER_nondet_float();
  x_2 = __VERIFIER_nondet_float();
  x_1 = __VERIFIER_nondet_float();
  _EL_U_97 = __VERIFIER_nondet_bool();

  bool __ok = (1 && ((( !(_EL_U_97 || ( !(( !(((x_2 + (-1.0 * x_3)) <= 10.0) && ((x_0 + (-1.0 * x_3)) <= 1.0))) || _EL_U_95)))) && ( !_J115)) && ( !_J121)));
  while (__steps_to_fair >= 0 && __ok) {
    if ((_J115 && _J121)) {
      __steps_to_fair = __VERIFIER_nondet_int();
    } else {
      __steps_to_fair--;
    }
    _x__J121 = __VERIFIER_nondet_bool();
    _x__J115 = __VERIFIER_nondet_bool();
    _x__EL_U_95 = __VERIFIER_nondet_bool();
    _x_x_3 = __VERIFIER_nondet_float();
    _x_x_0 = __VERIFIER_nondet_float();
    _x_x_2 = __VERIFIER_nondet_float();
    _x_x_1 = __VERIFIER_nondet_float();
    _x__EL_U_97 = __VERIFIER_nondet_bool();

    __ok = ((((((((x_0 + (-1.0 * _x_x_0)) <= -5.0) && ((x_1 + (-1.0 * _x_x_0)) <= -6.0)) && (((x_0 + (-1.0 * _x_x_0)) == -5.0) || ((x_1 + (-1.0 * _x_x_0)) == -6.0))) && ((((x_0 + (-1.0 * _x_x_1)) <= -15.0) && ((x_3 + (-1.0 * _x_x_1)) <= -7.0)) && (((x_0 + (-1.0 * _x_x_1)) == -15.0) || ((x_3 + (-1.0 * _x_x_1)) == -7.0)))) && ((((x_1 + (-1.0 * _x_x_2)) <= -1.0) && ((x_3 + (-1.0 * _x_x_2)) <= -10.0)) && (((x_1 + (-1.0 * _x_x_2)) == -1.0) || ((x_3 + (-1.0 * _x_x_2)) == -10.0)))) && ((((x_2 + (-1.0 * _x_x_3)) <= -5.0) && ((x_3 + (-1.0 * _x_x_3)) <= -9.0)) && (((x_2 + (-1.0 * _x_x_3)) == -5.0) || ((x_3 + (-1.0 * _x_x_3)) == -9.0)))) && ((((_EL_U_95 == (_x__EL_U_95 || ( !(((_x_x_0 + (-1.0 * _x_x_3)) <= 1.0) && ((_x_x_2 + (-1.0 * _x_x_3)) <= 10.0))))) && (_EL_U_97 == (_x__EL_U_97 || ( !(_x__EL_U_95 || ( !(((_x_x_0 + (-1.0 * _x_x_3)) <= 1.0) && ((_x_x_2 + (-1.0 * _x_x_3)) <= 10.0)))))))) && (_x__J115 == (( !(_J115 && _J121)) && ((_J115 && _J121) || ((( !(((x_2 + (-1.0 * x_3)) <= 10.0) && ((x_0 + (-1.0 * x_3)) <= 1.0))) || ( !(( !(((x_2 + (-1.0 * x_3)) <= 10.0) && ((x_0 + (-1.0 * x_3)) <= 1.0))) || _EL_U_95))) || _J115))))) && (_x__J121 == (( !(_J115 && _J121)) && ((_J115 && _J121) || ((( !(( !(((x_2 + (-1.0 * x_3)) <= 10.0) && ((x_0 + (-1.0 * x_3)) <= 1.0))) || _EL_U_95)) || ( !(_EL_U_97 || ( !(( !(((x_2 + (-1.0 * x_3)) <= 10.0) && ((x_0 + (-1.0 * x_3)) <= 1.0))) || _EL_U_95))))) || _J121))))));
    _J121 = _x__J121;
    _J115 = _x__J115;
    _EL_U_95 = _x__EL_U_95;
    x_3 = _x_x_3;
    x_0 = _x_x_0;
    x_2 = _x_x_2;
    x_1 = _x_x_1;
    _EL_U_97 = _x__EL_U_97;

  }
}
