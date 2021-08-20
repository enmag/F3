extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);
typedef enum {false, true} bool;
bool __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}

int main()
{
bool _EL_U_55, _x__EL_U_55;
float r, _x_r;
bool _EL_U_57, _x__EL_U_57;
float i, _x_i;
bool _J98, _x__J98;
bool _J92, _x__J92;
bool _J85, _x__J85;
bool _J79, _x__J79;
bool _EL_U_51, _x__EL_U_51;
float m_x_i, _x_m_x_i;
bool _EL_U_53, _x__EL_U_53;

  int __steps_to_fair = __VERIFIER_nondet_int();
  _EL_U_55 = __VERIFIER_nondet_bool();
  r = __VERIFIER_nondet_float();
  _EL_U_57 = __VERIFIER_nondet_bool();
  i = __VERIFIER_nondet_float();
  _J98 = __VERIFIER_nondet_bool();
  _J92 = __VERIFIER_nondet_bool();
  _J85 = __VERIFIER_nondet_bool();
  _J79 = __VERIFIER_nondet_bool();
  _EL_U_51 = __VERIFIER_nondet_bool();
  m_x_i = __VERIFIER_nondet_float();
  _EL_U_53 = __VERIFIER_nondet_bool();

  bool __ok = (((0.0 <= i) && (( !(r <= 0.0)) && ( !(10.0 <= r)))) && ((((( !((_EL_U_57 || ( !(( !(r <= i)) || _EL_U_55))) || (_EL_U_53 || ( !(( !(m_x_i <= i)) || _EL_U_51))))) && ( !_J79)) && ( !_J85)) && ( !_J92)) && ( !_J98)));
  while (__steps_to_fair >= 0 && __ok) {
    if ((((_J79 && _J85) && _J92) && _J98)) {
      __steps_to_fair = __VERIFIER_nondet_int();
    } else {
      __steps_to_fair--;
    }
    _x__EL_U_55 = __VERIFIER_nondet_bool();
    _x_r = __VERIFIER_nondet_float();
    _x__EL_U_57 = __VERIFIER_nondet_bool();
    _x_i = __VERIFIER_nondet_float();
    _x__J98 = __VERIFIER_nondet_bool();
    _x__J92 = __VERIFIER_nondet_bool();
    _x__J85 = __VERIFIER_nondet_bool();
    _x__J79 = __VERIFIER_nondet_bool();
    _x__EL_U_51 = __VERIFIER_nondet_bool();
    _x_m_x_i = __VERIFIER_nondet_float();
    _x__EL_U_53 = __VERIFIER_nondet_bool();

    __ok = (((((r == _x_r) && ((10.0 <= i) || ((i + (-1.0 * _x_i)) == -1.0))) && (( !(10.0 <= i)) || (_x_i == 0.0))) && (m_x_i == _x_i)) && ((((((_EL_U_53 == (_x__EL_U_53 || ( !(_x__EL_U_51 || ( !(_x_m_x_i <= _x_i)))))) && ((_EL_U_51 == (_x__EL_U_51 || ( !(_x_m_x_i <= _x_i)))) && ((_EL_U_55 == (_x__EL_U_55 || ( !(_x_r <= _x_i)))) && (_EL_U_57 == (_x__EL_U_57 || ( !(_x__EL_U_55 || ( !(_x_r <= _x_i))))))))) && (_x__J79 == (( !(((_J79 && _J85) && _J92) && _J98)) && ((((_J79 && _J85) && _J92) && _J98) || ((( !(r <= i)) || ( !(( !(r <= i)) || _EL_U_55))) || _J79))))) && (_x__J85 == (( !(((_J79 && _J85) && _J92) && _J98)) && ((((_J79 && _J85) && _J92) && _J98) || ((( !(( !(r <= i)) || _EL_U_55)) || ( !(_EL_U_57 || ( !(( !(r <= i)) || _EL_U_55))))) || _J85))))) && (_x__J92 == (( !(((_J79 && _J85) && _J92) && _J98)) && ((((_J79 && _J85) && _J92) && _J98) || ((( !(m_x_i <= i)) || ( !(( !(m_x_i <= i)) || _EL_U_51))) || _J92))))) && (_x__J98 == (( !(((_J79 && _J85) && _J92) && _J98)) && ((((_J79 && _J85) && _J92) && _J98) || ((( !(( !(m_x_i <= i)) || _EL_U_51)) || ( !(_EL_U_53 || ( !(( !(m_x_i <= i)) || _EL_U_51))))) || _J98))))));
    _EL_U_55 = _x__EL_U_55;
    r = _x_r;
    _EL_U_57 = _x__EL_U_57;
    i = _x_i;
    _J98 = _x__J98;
    _J92 = _x__J92;
    _J85 = _x__J85;
    _J79 = _x__J79;
    _EL_U_51 = _x__EL_U_51;
    m_x_i = _x_m_x_i;
    _EL_U_53 = _x__EL_U_53;

  }
}
