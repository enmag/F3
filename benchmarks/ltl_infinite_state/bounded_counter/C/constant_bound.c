extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);
typedef enum {false, true} bool;
bool __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}

int main()
{
bool _EL_U_57, _x__EL_U_57;
float r, _x_r;
bool _EL_U_59, _x__EL_U_59;
float i, _x_i;
bool _J100, _x__J100;
bool _J94, _x__J94;
bool _J87, _x__J87;
bool _J81, _x__J81;
bool _EL_U_53, _x__EL_U_53;
float m_x_i, _x_m_x_i;
bool _EL_U_55, _x__EL_U_55;

  int __steps_to_fair = __VERIFIER_nondet_int();
  _EL_U_57 = __VERIFIER_nondet_bool();
  r = __VERIFIER_nondet_float();
  _EL_U_59 = __VERIFIER_nondet_bool();
  i = __VERIFIER_nondet_float();
  _J100 = __VERIFIER_nondet_bool();
  _J94 = __VERIFIER_nondet_bool();
  _J87 = __VERIFIER_nondet_bool();
  _J81 = __VERIFIER_nondet_bool();
  _EL_U_53 = __VERIFIER_nondet_bool();
  m_x_i = __VERIFIER_nondet_float();
  _EL_U_55 = __VERIFIER_nondet_bool();

  bool __ok = (((0.0 <= i) && (( !(r <= 0.0)) && ( !(10.0 <= r)))) && ((((( !((_EL_U_59 || ( !(( !(r <= i)) || _EL_U_57))) || (_EL_U_55 || ( !(( !(m_x_i <= i)) || _EL_U_53))))) && ( !_J81)) && ( !_J87)) && ( !_J94)) && ( !_J100)));
  while (__steps_to_fair >= 0 && __ok) {
    if ((((_J81 && _J87) && _J94) && _J100)) {
      __steps_to_fair = __VERIFIER_nondet_int();
    } else {
      __steps_to_fair--;
    }
    _x__EL_U_57 = __VERIFIER_nondet_bool();
    _x_r = __VERIFIER_nondet_float();
    _x__EL_U_59 = __VERIFIER_nondet_bool();
    _x_i = __VERIFIER_nondet_float();
    _x__J100 = __VERIFIER_nondet_bool();
    _x__J94 = __VERIFIER_nondet_bool();
    _x__J87 = __VERIFIER_nondet_bool();
    _x__J81 = __VERIFIER_nondet_bool();
    _x__EL_U_53 = __VERIFIER_nondet_bool();
    _x_m_x_i = __VERIFIER_nondet_float();
    _x__EL_U_55 = __VERIFIER_nondet_bool();

    __ok = (((((r == _x_r) && ((10.0 <= i) || (((i + (-1.0 * _x_i)) == -1.0) || (i == _x_i)))) && (( !(10.0 <= i)) || (_x_i == 0.0))) && (m_x_i == _x_i)) && ((((((_EL_U_55 == (_x__EL_U_55 || ( !(_x__EL_U_53 || ( !(_x_m_x_i <= _x_i)))))) && ((_EL_U_53 == (_x__EL_U_53 || ( !(_x_m_x_i <= _x_i)))) && ((_EL_U_57 == (_x__EL_U_57 || ( !(_x_r <= _x_i)))) && (_EL_U_59 == (_x__EL_U_59 || ( !(_x__EL_U_57 || ( !(_x_r <= _x_i))))))))) && (_x__J81 == (( !(((_J81 && _J87) && _J94) && _J100)) && ((((_J81 && _J87) && _J94) && _J100) || ((( !(r <= i)) || ( !(( !(r <= i)) || _EL_U_57))) || _J81))))) && (_x__J87 == (( !(((_J81 && _J87) && _J94) && _J100)) && ((((_J81 && _J87) && _J94) && _J100) || ((( !(( !(r <= i)) || _EL_U_57)) || ( !(_EL_U_59 || ( !(( !(r <= i)) || _EL_U_57))))) || _J87))))) && (_x__J94 == (( !(((_J81 && _J87) && _J94) && _J100)) && ((((_J81 && _J87) && _J94) && _J100) || ((( !(m_x_i <= i)) || ( !(( !(m_x_i <= i)) || _EL_U_53))) || _J94))))) && (_x__J100 == (( !(((_J81 && _J87) && _J94) && _J100)) && ((((_J81 && _J87) && _J94) && _J100) || ((( !(( !(m_x_i <= i)) || _EL_U_53)) || ( !(_EL_U_55 || ( !(( !(m_x_i <= i)) || _EL_U_53))))) || _J100))))));
    _EL_U_57 = _x__EL_U_57;
    r = _x_r;
    _EL_U_59 = _x__EL_U_59;
    i = _x_i;
    _J100 = _x__J100;
    _J94 = _x__J94;
    _J87 = _x__J87;
    _J81 = _x__J81;
    _EL_U_53 = _x__EL_U_53;
    m_x_i = _x_m_x_i;
    _EL_U_55 = _x__EL_U_55;

  }
}
