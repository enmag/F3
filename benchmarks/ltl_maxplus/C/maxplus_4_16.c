extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);
typedef enum {false, true} bool;
bool __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}

int main()
{
bool _J122, _x__J122;
bool _J114, _x__J114;
bool _EL_U_94, _x__EL_U_94;
float x_1, _x_x_1;
float x_0, _x_x_0;
float x_3, _x_x_3;
float x_2, _x_x_2;
bool _EL_U_96, _x__EL_U_96;
bool _EL_X_91, _x__EL_X_91;

  int __steps_to_fair = __VERIFIER_nondet_int();
  _J122 = __VERIFIER_nondet_bool();
  _J114 = __VERIFIER_nondet_bool();
  _EL_U_94 = __VERIFIER_nondet_bool();
  x_1 = __VERIFIER_nondet_float();
  x_0 = __VERIFIER_nondet_float();
  x_3 = __VERIFIER_nondet_float();
  x_2 = __VERIFIER_nondet_float();
  _EL_U_96 = __VERIFIER_nondet_bool();
  _EL_X_91 = __VERIFIER_nondet_bool();

  bool __ok = (1 && ((( !(_EL_X_91 || (_EL_U_96 && ( !(((x_0 + (-1.0 * x_1)) <= -17.0) || _EL_U_94))))) && ( !_J114)) && ( !_J122)));
  while (__steps_to_fair >= 0 && __ok) {
    if ((_J114 && _J122)) {
      __steps_to_fair = __VERIFIER_nondet_int();
    } else {
      __steps_to_fair--;
    }
    _x__J122 = __VERIFIER_nondet_bool();
    _x__J114 = __VERIFIER_nondet_bool();
    _x__EL_U_94 = __VERIFIER_nondet_bool();
    _x_x_1 = __VERIFIER_nondet_float();
    _x_x_0 = __VERIFIER_nondet_float();
    _x_x_3 = __VERIFIER_nondet_float();
    _x_x_2 = __VERIFIER_nondet_float();
    _x__EL_U_96 = __VERIFIER_nondet_bool();
    _x__EL_X_91 = __VERIFIER_nondet_bool();

    __ok = ((((((((x_2 + (-1.0 * _x_x_0)) <= -17.0) && ((x_3 + (-1.0 * _x_x_0)) <= -8.0)) && (((x_2 + (-1.0 * _x_x_0)) == -17.0) || ((x_3 + (-1.0 * _x_x_0)) == -8.0))) && ((((x_1 + (-1.0 * _x_x_1)) <= -18.0) && ((x_3 + (-1.0 * _x_x_1)) <= -13.0)) && (((x_1 + (-1.0 * _x_x_1)) == -18.0) || ((x_3 + (-1.0 * _x_x_1)) == -13.0)))) && ((((x_2 + (-1.0 * _x_x_2)) <= -14.0) && ((x_3 + (-1.0 * _x_x_2)) <= -3.0)) && (((x_2 + (-1.0 * _x_x_2)) == -14.0) || ((x_3 + (-1.0 * _x_x_2)) == -3.0)))) && ((((x_0 + (-1.0 * _x_x_3)) <= -5.0) && ((x_1 + (-1.0 * _x_x_3)) <= -12.0)) && (((x_0 + (-1.0 * _x_x_3)) == -5.0) || ((x_1 + (-1.0 * _x_x_3)) == -12.0)))) && ((((_EL_U_96 == (_x__EL_X_91 || (_x__EL_U_96 && ( !(_x__EL_U_94 || ((_x_x_0 + (-1.0 * _x_x_1)) <= -17.0)))))) && ((_EL_X_91 == (6.0 <= (_x_x_0 + (-1.0 * _x_x_1)))) && (_EL_U_94 == (_x__EL_U_94 || ((_x_x_0 + (-1.0 * _x_x_1)) <= -17.0))))) && (_x__J114 == (( !(_J114 && _J122)) && ((_J114 && _J122) || ((((x_0 + (-1.0 * x_1)) <= -17.0) || ( !(((x_0 + (-1.0 * x_1)) <= -17.0) || _EL_U_94))) || _J114))))) && (_x__J122 == (( !(_J114 && _J122)) && ((_J114 && _J122) || ((_EL_X_91 || ( !(_EL_X_91 || (_EL_U_96 && ( !(((x_0 + (-1.0 * x_1)) <= -17.0) || _EL_U_94)))))) || _J122))))));
    _J122 = _x__J122;
    _J114 = _x__J114;
    _EL_U_94 = _x__EL_U_94;
    x_1 = _x_x_1;
    x_0 = _x_x_0;
    x_3 = _x_x_3;
    x_2 = _x_x_2;
    _EL_U_96 = _x__EL_U_96;
    _EL_X_91 = _x__EL_X_91;

  }
}
