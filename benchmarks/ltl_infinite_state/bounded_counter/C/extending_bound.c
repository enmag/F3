extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);
typedef enum {false, true} bool;
bool __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}

int main()
{
bool _EL_U_68, _x__EL_U_68;
bool _EL_U_70, _x__EL_U_70;
float l, _x_l;
bool _EL_U_72, _x__EL_U_72;
bool inc_i, _x_inc_i;
float i, _x_i;
float r, _x_r;
bool _J111, _x__J111;
bool _J105, _x__J105;
bool _J100, _x__J100;
bool _J94, _x__J94;
bool _EL_U_66, _x__EL_U_66;

  int __steps_to_fair = __VERIFIER_nondet_int();
  _EL_U_68 = __VERIFIER_nondet_bool();
  _EL_U_70 = __VERIFIER_nondet_bool();
  l = __VERIFIER_nondet_float();
  _EL_U_72 = __VERIFIER_nondet_bool();
  inc_i = __VERIFIER_nondet_bool();
  i = __VERIFIER_nondet_float();
  r = __VERIFIER_nondet_float();
  _J111 = __VERIFIER_nondet_bool();
  _J105 = __VERIFIER_nondet_bool();
  _J100 = __VERIFIER_nondet_bool();
  _J94 = __VERIFIER_nondet_bool();
  _EL_U_66 = __VERIFIER_nondet_bool();

  bool __ok = ((((( !(r <= 0.0)) && ( !(l <= r))) && ((0.0 <= i) && ( !inc_i))) && ( !(l <= 0.0))) && ((((( !((_EL_U_72 || ( !(( !(r <= i)) || _EL_U_70))) || (_EL_U_68 || ( !(inc_i || _EL_U_66))))) && ( !_J94)) && ( !_J100)) && ( !_J105)) && ( !_J111)));
  while (__steps_to_fair >= 0 && __ok) {
    if ((((_J94 && _J100) && _J105) && _J111)) {
      __steps_to_fair = __VERIFIER_nondet_int();
    } else {
      __steps_to_fair--;
    }
    _x__EL_U_68 = __VERIFIER_nondet_bool();
    _x__EL_U_70 = __VERIFIER_nondet_bool();
    _x_l = __VERIFIER_nondet_float();
    _x__EL_U_72 = __VERIFIER_nondet_bool();
    _x_inc_i = __VERIFIER_nondet_bool();
    _x_i = __VERIFIER_nondet_float();
    _x_r = __VERIFIER_nondet_float();
    _x__J111 = __VERIFIER_nondet_bool();
    _x__J105 = __VERIFIER_nondet_bool();
    _x__J100 = __VERIFIER_nondet_bool();
    _x__J94 = __VERIFIER_nondet_bool();
    _x__EL_U_66 = __VERIFIER_nondet_bool();

    __ok = ((((r == _x_r) && ((l <= i) || (((_x_inc_i && ((i + (-1.0 * _x_i)) == -1.0)) || (( !_x_inc_i) && (i == _x_i))) && (l == _x_l)))) && (( !(l <= i)) || (( !_x_inc_i) && ((_x_i == 0.0) && ((l + (-1.0 * _x_l)) == -1.0))))) && ((((((_EL_U_68 == (_x__EL_U_68 || ( !(_x_inc_i || _x__EL_U_66)))) && ((_EL_U_66 == (_x_inc_i || _x__EL_U_66)) && ((_EL_U_70 == (_x__EL_U_70 || ( !(_x_r <= _x_i)))) && (_EL_U_72 == (_x__EL_U_72 || ( !(_x__EL_U_70 || ( !(_x_r <= _x_i))))))))) && (_x__J94 == (( !(((_J94 && _J100) && _J105) && _J111)) && ((((_J94 && _J100) && _J105) && _J111) || ((( !(r <= i)) || ( !(( !(r <= i)) || _EL_U_70))) || _J94))))) && (_x__J100 == (( !(((_J94 && _J100) && _J105) && _J111)) && ((((_J94 && _J100) && _J105) && _J111) || ((( !(( !(r <= i)) || _EL_U_70)) || ( !(_EL_U_72 || ( !(( !(r <= i)) || _EL_U_70))))) || _J100))))) && (_x__J105 == (( !(((_J94 && _J100) && _J105) && _J111)) && ((((_J94 && _J100) && _J105) && _J111) || ((inc_i || ( !(inc_i || _EL_U_66))) || _J105))))) && (_x__J111 == (( !(((_J94 && _J100) && _J105) && _J111)) && ((((_J94 && _J100) && _J105) && _J111) || ((( !(inc_i || _EL_U_66)) || ( !(_EL_U_68 || ( !(inc_i || _EL_U_66))))) || _J111))))));
    _EL_U_68 = _x__EL_U_68;
    _EL_U_70 = _x__EL_U_70;
    l = _x_l;
    _EL_U_72 = _x__EL_U_72;
    inc_i = _x_inc_i;
    i = _x_i;
    r = _x_r;
    _J111 = _x__J111;
    _J105 = _x__J105;
    _J100 = _x__J100;
    _J94 = _x__J94;
    _EL_U_66 = _x__EL_U_66;

  }
}
