extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);
typedef enum {false, true} bool;
bool __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}

int main()
{
bool _J134, _x__J134;
bool _EL_U_109, _x__EL_U_109;
float _diverge_delta, _x__diverge_delta;
float delta, _x_delta;
float h, _x_h;
bool _EL_U_111, _x__EL_U_111;
bool _EL_U_113, _x__EL_U_113;
float v, _x_v;
bool _EL_U_115, _x__EL_U_115;
bool _J152, _x__J152;
bool _J146, _x__J146;
bool _J140, _x__J140;

  int __steps_to_fair = __VERIFIER_nondet_int();
  _J134 = __VERIFIER_nondet_bool();
  _EL_U_109 = __VERIFIER_nondet_bool();
  _diverge_delta = __VERIFIER_nondet_float();
  delta = __VERIFIER_nondet_float();
  h = __VERIFIER_nondet_float();
  _EL_U_111 = __VERIFIER_nondet_bool();
  _EL_U_113 = __VERIFIER_nondet_bool();
  v = __VERIFIER_nondet_float();
  _EL_U_115 = __VERIFIER_nondet_bool();
  _J152 = __VERIFIER_nondet_bool();
  _J146 = __VERIFIER_nondet_bool();
  _J140 = __VERIFIER_nondet_bool();

  bool __ok = (((((((h == 0.0) && (v == (981.0/100.0))) && ((delta == 0.0) || ( !((h == 0.0) && ( !(0.0 <= v)))))) && (0.0 <= delta)) && (0.0 <= h)) && (delta == _diverge_delta)) && ((((( !((_EL_U_115 || ( !((h == 0.0) || _EL_U_113))) || (_EL_U_111 || ( !((1.0 <= _diverge_delta) || _EL_U_109))))) && ( !_J134)) && ( !_J140)) && ( !_J146)) && ( !_J152)));
  while (__steps_to_fair >= 0 && __ok) {
    if ((((_J134 && _J140) && _J146) && _J152)) {
      __steps_to_fair = __VERIFIER_nondet_int();
    } else {
      __steps_to_fair--;
    }
    _x__J134 = __VERIFIER_nondet_bool();
    _x__EL_U_109 = __VERIFIER_nondet_bool();
    _x__diverge_delta = __VERIFIER_nondet_float();
    _x_delta = __VERIFIER_nondet_float();
    _x_h = __VERIFIER_nondet_float();
    _x__EL_U_111 = __VERIFIER_nondet_bool();
    _x__EL_U_113 = __VERIFIER_nondet_bool();
    _x_v = __VERIFIER_nondet_float();
    _x__EL_U_115 = __VERIFIER_nondet_bool();
    _x__J152 = __VERIFIER_nondet_bool();
    _x__J146 = __VERIFIER_nondet_bool();
    _x__J140 = __VERIFIER_nondet_bool();

    __ok = ((((((((_x_delta == 0.0) || ( !((_x_h == 0.0) && ( !(0.0 <= _x_v))))) && (0.0 <= _x_delta)) && (0.0 <= _x_h)) && ((( !((h == 0.0) && ( !(0.0 <= v)))) || (_x_h == 0.0)) && (((h == 0.0) && ( !(0.0 <= v))) || (((200.0 * h) + ((-200.0 * _x_h) + ((-981.0 * (delta * delta)) + (200.0 * (v * delta))))) == 0.0)))) && ((( !((h == 0.0) && ( !(0.0 <= v)))) || ((v + _x_v) == 0.0)) && (((h == 0.0) && ( !(0.0 <= v))) || (((100.0 * v) + ((-100.0 * _x_v) + (-981.0 * delta))) == 0.0)))) && (((delta == _x__diverge_delta) || ( !(1.0 <= _diverge_delta))) && ((1.0 <= _diverge_delta) || ((delta + (_diverge_delta + (-1.0 * _x__diverge_delta))) == 0.0)))) && ((((((_EL_U_111 == (_x__EL_U_111 || ( !(_x__EL_U_109 || (1.0 <= _x__diverge_delta))))) && ((_EL_U_109 == (_x__EL_U_109 || (1.0 <= _x__diverge_delta))) && ((_EL_U_113 == ((_x_h == 0.0) || _x__EL_U_113)) && (_EL_U_115 == (_x__EL_U_115 || ( !((_x_h == 0.0) || _x__EL_U_113))))))) && (_x__J134 == (( !(((_J134 && _J140) && _J146) && _J152)) && ((((_J134 && _J140) && _J146) && _J152) || (((h == 0.0) || ( !((h == 0.0) || _EL_U_113))) || _J134))))) && (_x__J140 == (( !(((_J134 && _J140) && _J146) && _J152)) && ((((_J134 && _J140) && _J146) && _J152) || ((( !((h == 0.0) || _EL_U_113)) || ( !(_EL_U_115 || ( !((h == 0.0) || _EL_U_113))))) || _J140))))) && (_x__J146 == (( !(((_J134 && _J140) && _J146) && _J152)) && ((((_J134 && _J140) && _J146) && _J152) || (((1.0 <= _diverge_delta) || ( !((1.0 <= _diverge_delta) || _EL_U_109))) || _J146))))) && (_x__J152 == (( !(((_J134 && _J140) && _J146) && _J152)) && ((((_J134 && _J140) && _J146) && _J152) || ((( !((1.0 <= _diverge_delta) || _EL_U_109)) || ( !(_EL_U_111 || ( !((1.0 <= _diverge_delta) || _EL_U_109))))) || _J152))))));
    _J134 = _x__J134;
    _EL_U_109 = _x__EL_U_109;
    _diverge_delta = _x__diverge_delta;
    delta = _x_delta;
    h = _x_h;
    _EL_U_111 = _x__EL_U_111;
    _EL_U_113 = _x__EL_U_113;
    v = _x_v;
    _EL_U_115 = _x__EL_U_115;
    _J152 = _x__J152;
    _J146 = _x__J146;
    _J140 = _x__J140;

  }
}
