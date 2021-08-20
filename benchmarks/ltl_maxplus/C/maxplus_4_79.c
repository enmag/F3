extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);
typedef enum {false, true} bool;
bool __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}

int main()
{
bool _J121, _x__J121;
float x_1, _x_x_1;
bool _J111, _x__J111;
bool _EL_U_93, _x__EL_U_93;
float x_2, _x_x_2;
float x_0, _x_x_0;
float x_3, _x_x_3;
bool _EL_U_96, _x__EL_U_96;

  int __steps_to_fair = __VERIFIER_nondet_int();
  _J121 = __VERIFIER_nondet_bool();
  x_1 = __VERIFIER_nondet_float();
  _J111 = __VERIFIER_nondet_bool();
  _EL_U_93 = __VERIFIER_nondet_bool();
  x_2 = __VERIFIER_nondet_float();
  x_0 = __VERIFIER_nondet_float();
  x_3 = __VERIFIER_nondet_float();
  _EL_U_96 = __VERIFIER_nondet_bool();

  bool __ok = (1 && ((( !(_EL_U_96 || ((18.0 <= (x_0 + (-1.0 * x_3))) && ( !(( !(3.0 <= (x_0 + (-1.0 * x_2)))) || _EL_U_93))))) && ( !_J111)) && ( !_J121)));
  while (__steps_to_fair >= 0 && __ok) {
    if ((_J111 && _J121)) {
      __steps_to_fair = __VERIFIER_nondet_int();
    } else {
      __steps_to_fair--;
    }
    _x__J121 = __VERIFIER_nondet_bool();
    _x_x_1 = __VERIFIER_nondet_float();
    _x__J111 = __VERIFIER_nondet_bool();
    _x__EL_U_93 = __VERIFIER_nondet_bool();
    _x_x_2 = __VERIFIER_nondet_float();
    _x_x_0 = __VERIFIER_nondet_float();
    _x_x_3 = __VERIFIER_nondet_float();
    _x__EL_U_96 = __VERIFIER_nondet_bool();

    __ok = ((((((((x_1 + (-1.0 * _x_x_0)) <= -11.0) && ((x_3 + (-1.0 * _x_x_0)) <= -1.0)) && (((x_1 + (-1.0 * _x_x_0)) == -11.0) || ((x_3 + (-1.0 * _x_x_0)) == -1.0))) && ((((x_0 + (-1.0 * _x_x_1)) <= -8.0) && ((x_2 + (-1.0 * _x_x_1)) <= -20.0)) && (((x_0 + (-1.0 * _x_x_1)) == -8.0) || ((x_2 + (-1.0 * _x_x_1)) == -20.0)))) && ((((x_0 + (-1.0 * _x_x_2)) <= -14.0) && ((x_1 + (-1.0 * _x_x_2)) <= -19.0)) && (((x_0 + (-1.0 * _x_x_2)) == -14.0) || ((x_1 + (-1.0 * _x_x_2)) == -19.0)))) && ((((x_0 + (-1.0 * _x_x_3)) <= -18.0) && ((x_1 + (-1.0 * _x_x_3)) <= -20.0)) && (((x_0 + (-1.0 * _x_x_3)) == -18.0) || ((x_1 + (-1.0 * _x_x_3)) == -20.0)))) && ((((_EL_U_93 == (_x__EL_U_93 || ( !(3.0 <= (_x_x_0 + (-1.0 * _x_x_2)))))) && (_EL_U_96 == (_x__EL_U_96 || (( !(_x__EL_U_93 || ( !(3.0 <= (_x_x_0 + (-1.0 * _x_x_2)))))) && (18.0 <= (_x_x_0 + (-1.0 * _x_x_3))))))) && (_x__J111 == (( !(_J111 && _J121)) && ((_J111 && _J121) || ((( !(3.0 <= (x_0 + (-1.0 * x_2)))) || ( !(( !(3.0 <= (x_0 + (-1.0 * x_2)))) || _EL_U_93))) || _J111))))) && (_x__J121 == (( !(_J111 && _J121)) && ((_J111 && _J121) || ((((18.0 <= (x_0 + (-1.0 * x_3))) && ( !(( !(3.0 <= (x_0 + (-1.0 * x_2)))) || _EL_U_93))) || ( !(_EL_U_96 || ((18.0 <= (x_0 + (-1.0 * x_3))) && ( !(( !(3.0 <= (x_0 + (-1.0 * x_2)))) || _EL_U_93)))))) || _J121))))));
    _J121 = _x__J121;
    x_1 = _x_x_1;
    _J111 = _x__J111;
    _EL_U_93 = _x__EL_U_93;
    x_2 = _x_x_2;
    x_0 = _x_x_0;
    x_3 = _x_x_3;
    _EL_U_96 = _x__EL_U_96;

  }
}
