extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);
typedef enum {false, true} bool;
bool __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}

int main()
{
bool _J122, _x__J122;
bool _J116, _x__J116;
bool _EL_U_99, _x__EL_U_99;
float x_2, _x_x_2;
float x_1, _x_x_1;
bool _EL_U_101, _x__EL_U_101;
float x_3, _x_x_3;
float x_0, _x_x_0;

  int __steps_to_fair = __VERIFIER_nondet_int();
  _J122 = __VERIFIER_nondet_bool();
  _J116 = __VERIFIER_nondet_bool();
  _EL_U_99 = __VERIFIER_nondet_bool();
  x_2 = __VERIFIER_nondet_float();
  x_1 = __VERIFIER_nondet_float();
  _EL_U_101 = __VERIFIER_nondet_bool();
  x_3 = __VERIFIER_nondet_float();
  x_0 = __VERIFIER_nondet_float();

  bool __ok = (1 && ((( !((-6.0 <= (x_0 + (-1.0 * x_3))) && (_EL_U_101 || ( !((-6.0 <= (x_1 + (-1.0 * x_2))) || _EL_U_99))))) && ( !_J116)) && ( !_J122)));
  while (__steps_to_fair >= 0 && __ok) {
    if ((_J116 && _J122)) {
      __steps_to_fair = __VERIFIER_nondet_int();
    } else {
      __steps_to_fair--;
    }
    _x__J122 = __VERIFIER_nondet_bool();
    _x__J116 = __VERIFIER_nondet_bool();
    _x__EL_U_99 = __VERIFIER_nondet_bool();
    _x_x_2 = __VERIFIER_nondet_float();
    _x_x_1 = __VERIFIER_nondet_float();
    _x__EL_U_101 = __VERIFIER_nondet_bool();
    _x_x_3 = __VERIFIER_nondet_float();
    _x_x_0 = __VERIFIER_nondet_float();

    __ok = ((((((((x_0 + (-1.0 * _x_x_0)) <= -19.0) && ((x_1 + (-1.0 * _x_x_0)) <= -10.0)) && (((x_0 + (-1.0 * _x_x_0)) == -19.0) || ((x_1 + (-1.0 * _x_x_0)) == -10.0))) && ((((x_0 + (-1.0 * _x_x_1)) <= -20.0) && ((x_3 + (-1.0 * _x_x_1)) <= -2.0)) && (((x_0 + (-1.0 * _x_x_1)) == -20.0) || ((x_3 + (-1.0 * _x_x_1)) == -2.0)))) && ((((x_1 + (-1.0 * _x_x_2)) <= -14.0) && ((x_2 + (-1.0 * _x_x_2)) <= -12.0)) && (((x_1 + (-1.0 * _x_x_2)) == -14.0) || ((x_2 + (-1.0 * _x_x_2)) == -12.0)))) && ((((x_2 + (-1.0 * _x_x_3)) <= -8.0) && ((x_3 + (-1.0 * _x_x_3)) <= -9.0)) && (((x_2 + (-1.0 * _x_x_3)) == -8.0) || ((x_3 + (-1.0 * _x_x_3)) == -9.0)))) && ((((_EL_U_99 == (_x__EL_U_99 || (-6.0 <= (_x_x_1 + (-1.0 * _x_x_2))))) && (_EL_U_101 == (_x__EL_U_101 || ( !(_x__EL_U_99 || (-6.0 <= (_x_x_1 + (-1.0 * _x_x_2)))))))) && (_x__J116 == (( !(_J116 && _J122)) && ((_J116 && _J122) || (((-6.0 <= (x_1 + (-1.0 * x_2))) || ( !((-6.0 <= (x_1 + (-1.0 * x_2))) || _EL_U_99))) || _J116))))) && (_x__J122 == (( !(_J116 && _J122)) && ((_J116 && _J122) || ((( !((-6.0 <= (x_1 + (-1.0 * x_2))) || _EL_U_99)) || ( !(_EL_U_101 || ( !((-6.0 <= (x_1 + (-1.0 * x_2))) || _EL_U_99))))) || _J122))))));
    _J122 = _x__J122;
    _J116 = _x__J116;
    _EL_U_99 = _x__EL_U_99;
    x_2 = _x_x_2;
    x_1 = _x_x_1;
    _EL_U_101 = _x__EL_U_101;
    x_3 = _x_x_3;
    x_0 = _x_x_0;

  }
}
