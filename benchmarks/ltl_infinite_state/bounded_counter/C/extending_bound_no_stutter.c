extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);
typedef enum {false, true} bool;
bool __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}

int main()
{
bool _EL_U_65, _x__EL_U_65;
bool _EL_U_67, _x__EL_U_67;
float l, _x_l;
bool _EL_U_69, _x__EL_U_69;
bool inc_i, _x_inc_i;
float i, _x_i;
float r, _x_r;
bool _J108, _x__J108;
bool _J102, _x__J102;
bool _J97, _x__J97;
bool _J91, _x__J91;
bool _EL_U_63, _x__EL_U_63;

  int __steps_to_fair = __VERIFIER_nondet_int();
  _EL_U_65 = __VERIFIER_nondet_bool();
  _EL_U_67 = __VERIFIER_nondet_bool();
  l = __VERIFIER_nondet_float();
  _EL_U_69 = __VERIFIER_nondet_bool();
  inc_i = __VERIFIER_nondet_bool();
  i = __VERIFIER_nondet_float();
  r = __VERIFIER_nondet_float();
  _J108 = __VERIFIER_nondet_bool();
  _J102 = __VERIFIER_nondet_bool();
  _J97 = __VERIFIER_nondet_bool();
  _J91 = __VERIFIER_nondet_bool();
  _EL_U_63 = __VERIFIER_nondet_bool();

  bool __ok = ((((( !(r <= 0.0)) && ( !(l <= r))) && ((0.0 <= i) && ( !inc_i))) && ( !(l <= 0.0))) && ((((( !((_EL_U_69 || ( !(( !(r <= i)) || _EL_U_67))) || (_EL_U_65 || ( !(inc_i || _EL_U_63))))) && ( !_J91)) && ( !_J97)) && ( !_J102)) && ( !_J108)));
  while (__steps_to_fair >= 0 && __ok) {
    if ((((_J91 && _J97) && _J102) && _J108)) {
      __steps_to_fair = __VERIFIER_nondet_int();
    } else {
      __steps_to_fair--;
    }
    _x__EL_U_65 = __VERIFIER_nondet_bool();
    _x__EL_U_67 = __VERIFIER_nondet_bool();
    _x_l = __VERIFIER_nondet_float();
    _x__EL_U_69 = __VERIFIER_nondet_bool();
    _x_inc_i = __VERIFIER_nondet_bool();
    _x_i = __VERIFIER_nondet_float();
    _x_r = __VERIFIER_nondet_float();
    _x__J108 = __VERIFIER_nondet_bool();
    _x__J102 = __VERIFIER_nondet_bool();
    _x__J97 = __VERIFIER_nondet_bool();
    _x__J91 = __VERIFIER_nondet_bool();
    _x__EL_U_63 = __VERIFIER_nondet_bool();

    __ok = ((((r == _x_r) && ((l <= i) || (((i + (-1.0 * _x_i)) == -1.0) && (_x_inc_i && (l == _x_l))))) && (( !(l <= i)) || ((_x_i == 0.0) && (((l + (-1.0 * _x_l)) == -1.0) && ( !_x_inc_i))))) && ((((((_EL_U_65 == (_x__EL_U_65 || ( !(_x_inc_i || _x__EL_U_63)))) && ((_EL_U_63 == (_x_inc_i || _x__EL_U_63)) && ((_EL_U_67 == (_x__EL_U_67 || ( !(_x_r <= _x_i)))) && (_EL_U_69 == (_x__EL_U_69 || ( !(_x__EL_U_67 || ( !(_x_r <= _x_i))))))))) && (_x__J91 == (( !(((_J91 && _J97) && _J102) && _J108)) && ((((_J91 && _J97) && _J102) && _J108) || ((( !(r <= i)) || ( !(( !(r <= i)) || _EL_U_67))) || _J91))))) && (_x__J97 == (( !(((_J91 && _J97) && _J102) && _J108)) && ((((_J91 && _J97) && _J102) && _J108) || ((( !(( !(r <= i)) || _EL_U_67)) || ( !(_EL_U_69 || ( !(( !(r <= i)) || _EL_U_67))))) || _J97))))) && (_x__J102 == (( !(((_J91 && _J97) && _J102) && _J108)) && ((((_J91 && _J97) && _J102) && _J108) || ((inc_i || ( !(inc_i || _EL_U_63))) || _J102))))) && (_x__J108 == (( !(((_J91 && _J97) && _J102) && _J108)) && ((((_J91 && _J97) && _J102) && _J108) || ((( !(inc_i || _EL_U_63)) || ( !(_EL_U_65 || ( !(inc_i || _EL_U_63))))) || _J108))))));
    _EL_U_65 = _x__EL_U_65;
    _EL_U_67 = _x__EL_U_67;
    l = _x_l;
    _EL_U_69 = _x__EL_U_69;
    inc_i = _x_inc_i;
    i = _x_i;
    r = _x_r;
    _J108 = _x__J108;
    _J102 = _x__J102;
    _J97 = _x__J97;
    _J91 = _x__J91;
    _EL_U_63 = _x__EL_U_63;

  }
}
