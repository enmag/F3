extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);
typedef enum {false, true} bool;
bool __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}

int main()
{
bool _J139, _x__J139;
bool _EL_U_114, _x__EL_U_114;
float _diverge_delta, _x__diverge_delta;
float delta, _x_delta;
float h, _x_h;
bool _EL_U_116, _x__EL_U_116;
bool _EL_U_118, _x__EL_U_118;
float v, _x_v;
bool _EL_U_120, _x__EL_U_120;
bool _J157, _x__J157;
bool _J151, _x__J151;
bool _J145, _x__J145;

  int __steps_to_fair = __VERIFIER_nondet_int();
  _J139 = __VERIFIER_nondet_bool();
  _EL_U_114 = __VERIFIER_nondet_bool();
  _diverge_delta = __VERIFIER_nondet_float();
  delta = __VERIFIER_nondet_float();
  h = __VERIFIER_nondet_float();
  _EL_U_116 = __VERIFIER_nondet_bool();
  _EL_U_118 = __VERIFIER_nondet_bool();
  v = __VERIFIER_nondet_float();
  _EL_U_120 = __VERIFIER_nondet_bool();
  _J157 = __VERIFIER_nondet_bool();
  _J151 = __VERIFIER_nondet_bool();
  _J145 = __VERIFIER_nondet_bool();

  bool __ok = (((((((h == 0.0) && (v == (981.0/100.0))) && ((delta == 0.0) || ( !((h == 0.0) && ( !(0.0 <= v)))))) && (0.0 <= delta)) && (0.0 <= h)) && (delta == _diverge_delta)) && ((((( !((_EL_U_120 || ( !((h == 0.0) || _EL_U_118))) || (_EL_U_116 || ( !((1.0 <= _diverge_delta) || _EL_U_114))))) && ( !_J139)) && ( !_J145)) && ( !_J151)) && ( !_J157)));
  while (__steps_to_fair >= 0 && __ok) {
    if ((((_J139 && _J145) && _J151) && _J157)) {
      __steps_to_fair = __VERIFIER_nondet_int();
    } else {
      __steps_to_fair--;
    }
    _x__J139 = __VERIFIER_nondet_bool();
    _x__EL_U_114 = __VERIFIER_nondet_bool();
    _x__diverge_delta = __VERIFIER_nondet_float();
    _x_delta = __VERIFIER_nondet_float();
    _x_h = __VERIFIER_nondet_float();
    _x__EL_U_116 = __VERIFIER_nondet_bool();
    _x__EL_U_118 = __VERIFIER_nondet_bool();
    _x_v = __VERIFIER_nondet_float();
    _x__EL_U_120 = __VERIFIER_nondet_bool();
    _x__J157 = __VERIFIER_nondet_bool();
    _x__J151 = __VERIFIER_nondet_bool();
    _x__J145 = __VERIFIER_nondet_bool();

    __ok = ((((((((_x_delta == 0.0) || ( !((_x_h == 0.0) && ( !(0.0 <= _x_v))))) && (0.0 <= _x_delta)) && (0.0 <= _x_h)) && ((( !((h == 0.0) && ( !(0.0 <= v)))) || (_x_h == 0.0)) && (((h == 0.0) && ( !(0.0 <= v))) || (((200.0 * h) + ((-200.0 * _x_h) + ((-981.0 * (delta * delta)) + (200.0 * (v * delta))))) == 0.0)))) && ((( !((h == 0.0) && ( !(0.0 <= v)))) || (((11.0 * v) + (10.0 * _x_v)) == 0.0)) && (((h == 0.0) && ( !(0.0 <= v))) || (((100.0 * v) + ((-100.0 * _x_v) + (-981.0 * delta))) == 0.0)))) && (((delta == _x__diverge_delta) || ( !(1.0 <= _diverge_delta))) && ((1.0 <= _diverge_delta) || ((delta + (_diverge_delta + (-1.0 * _x__diverge_delta))) == 0.0)))) && ((((((_EL_U_116 == (_x__EL_U_116 || ( !(_x__EL_U_114 || (1.0 <= _x__diverge_delta))))) && ((_EL_U_114 == (_x__EL_U_114 || (1.0 <= _x__diverge_delta))) && ((_EL_U_118 == ((_x_h == 0.0) || _x__EL_U_118)) && (_EL_U_120 == (_x__EL_U_120 || ( !((_x_h == 0.0) || _x__EL_U_118))))))) && (_x__J139 == (( !(((_J139 && _J145) && _J151) && _J157)) && ((((_J139 && _J145) && _J151) && _J157) || (((h == 0.0) || ( !((h == 0.0) || _EL_U_118))) || _J139))))) && (_x__J145 == (( !(((_J139 && _J145) && _J151) && _J157)) && ((((_J139 && _J145) && _J151) && _J157) || ((( !((h == 0.0) || _EL_U_118)) || ( !(_EL_U_120 || ( !((h == 0.0) || _EL_U_118))))) || _J145))))) && (_x__J151 == (( !(((_J139 && _J145) && _J151) && _J157)) && ((((_J139 && _J145) && _J151) && _J157) || (((1.0 <= _diverge_delta) || ( !((1.0 <= _diverge_delta) || _EL_U_114))) || _J151))))) && (_x__J157 == (( !(((_J139 && _J145) && _J151) && _J157)) && ((((_J139 && _J145) && _J151) && _J157) || ((( !((1.0 <= _diverge_delta) || _EL_U_114)) || ( !(_EL_U_116 || ( !((1.0 <= _diverge_delta) || _EL_U_114))))) || _J157))))));
    _J139 = _x__J139;
    _EL_U_114 = _x__EL_U_114;
    _diverge_delta = _x__diverge_delta;
    delta = _x_delta;
    h = _x_h;
    _EL_U_116 = _x__EL_U_116;
    _EL_U_118 = _x__EL_U_118;
    v = _x_v;
    _EL_U_120 = _x__EL_U_120;
    _J157 = _x__J157;
    _J151 = _x__J151;
    _J145 = _x__J145;

  }
}
