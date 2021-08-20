extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);
typedef enum {false, true} bool;
bool __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}

int main()
{
bool _EL_U_82, _x__EL_U_82;
float _diverge_delta, _x__diverge_delta;
float delta, _x_delta;
bool _EL_U_84, _x__EL_U_84;
int bound, _x_bound;
float c, _x_c;
bool dec_bound, _x_dec_bound;
bool _J121, _x__J121;
bool _J115, _x__J115;
bool _J109, _x__J109;
bool _J103, _x__J103;
bool _EL_U_77, _x__EL_U_77;
bool _EL_U_79, _x__EL_U_79;

  int __steps_to_fair = __VERIFIER_nondet_int();
  _EL_U_82 = __VERIFIER_nondet_bool();
  _diverge_delta = __VERIFIER_nondet_float();
  delta = __VERIFIER_nondet_float();
  _EL_U_84 = __VERIFIER_nondet_bool();
  bound = __VERIFIER_nondet_int();
  c = __VERIFIER_nondet_float();
  dec_bound = __VERIFIER_nondet_bool();
  _J121 = __VERIFIER_nondet_bool();
  _J115 = __VERIFIER_nondet_bool();
  _J109 = __VERIFIER_nondet_bool();
  _J103 = __VERIFIER_nondet_bool();
  _EL_U_77 = __VERIFIER_nondet_bool();
  _EL_U_79 = __VERIFIER_nondet_bool();

  bool __ok = ((((dec_bound && (0.0 <= delta)) && (c <= ((float)(bound)))) && (delta == _diverge_delta)) && ((((( !((_EL_U_84 || ( !(( !dec_bound) || _EL_U_82))) || (_EL_U_79 || ( !((1.0 <= _diverge_delta) || _EL_U_77))))) && ( !_J103)) && ( !_J109)) && ( !_J115)) && ( !_J121)));
  while (__steps_to_fair >= 0 && __ok) {
    if ((((_J103 && _J109) && _J115) && _J121)) {
      __steps_to_fair = __VERIFIER_nondet_int();
    } else {
      __steps_to_fair--;
    }
    _x__EL_U_82 = __VERIFIER_nondet_bool();
    _x__diverge_delta = __VERIFIER_nondet_float();
    _x_delta = __VERIFIER_nondet_float();
    _x__EL_U_84 = __VERIFIER_nondet_bool();
    _x_bound = __VERIFIER_nondet_int();
    _x_c = __VERIFIER_nondet_float();
    _x_dec_bound = __VERIFIER_nondet_bool();
    _x__J121 = __VERIFIER_nondet_bool();
    _x__J115 = __VERIFIER_nondet_bool();
    _x__J109 = __VERIFIER_nondet_bool();
    _x__J103 = __VERIFIER_nondet_bool();
    _x__EL_U_77 = __VERIFIER_nondet_bool();
    _x__EL_U_79 = __VERIFIER_nondet_bool();

    __ok = ((((((((0.0 <= _x_delta) && (_x_c <= ((float)(_x_bound)))) && ((delta <= 0.0) || (((c + ((-1.0 * _x_c) + delta)) == 0.0) && (_x_dec_bound && (bound == _x_bound))))) && ((c == _x_c) || ( !(delta == 0.0)))) && ((_x_dec_bound && (bound == _x_bound)) || ( !((delta == 0.0) && ( !(((float)(bound)) <= c)))))) && ((_x_bound <= bound) || ( !_x_dec_bound))) && (((delta == _x__diverge_delta) || ( !(1.0 <= _diverge_delta))) && ((1.0 <= _diverge_delta) || ((delta + (_diverge_delta + (-1.0 * _x__diverge_delta))) == 0.0)))) && ((((((_EL_U_79 == (_x__EL_U_79 || ( !(_x__EL_U_77 || (1.0 <= _x__diverge_delta))))) && ((_EL_U_77 == (_x__EL_U_77 || (1.0 <= _x__diverge_delta))) && ((_EL_U_82 == (( !_x_dec_bound) || _x__EL_U_82)) && (_EL_U_84 == (_x__EL_U_84 || ( !(( !_x_dec_bound) || _x__EL_U_82))))))) && (_x__J103 == (( !(((_J103 && _J109) && _J115) && _J121)) && ((((_J103 && _J109) && _J115) && _J121) || ((( !dec_bound) || ( !(( !dec_bound) || _EL_U_82))) || _J103))))) && (_x__J109 == (( !(((_J103 && _J109) && _J115) && _J121)) && ((((_J103 && _J109) && _J115) && _J121) || ((( !(( !dec_bound) || _EL_U_82)) || ( !(_EL_U_84 || ( !(( !dec_bound) || _EL_U_82))))) || _J109))))) && (_x__J115 == (( !(((_J103 && _J109) && _J115) && _J121)) && ((((_J103 && _J109) && _J115) && _J121) || (((1.0 <= _diverge_delta) || ( !((1.0 <= _diverge_delta) || _EL_U_77))) || _J115))))) && (_x__J121 == (( !(((_J103 && _J109) && _J115) && _J121)) && ((((_J103 && _J109) && _J115) && _J121) || ((( !((1.0 <= _diverge_delta) || _EL_U_77)) || ( !(_EL_U_79 || ( !((1.0 <= _diverge_delta) || _EL_U_77))))) || _J121))))));
    _EL_U_82 = _x__EL_U_82;
    _diverge_delta = _x__diverge_delta;
    delta = _x_delta;
    _EL_U_84 = _x__EL_U_84;
    bound = _x_bound;
    c = _x_c;
    dec_bound = _x_dec_bound;
    _J121 = _x__J121;
    _J115 = _x__J115;
    _J109 = _x__J109;
    _J103 = _x__J103;
    _EL_U_77 = _x__EL_U_77;
    _EL_U_79 = _x__EL_U_79;

  }
}
