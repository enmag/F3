extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);
typedef enum {false, true} bool;
bool __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}

int main()
{
bool _EL_U_128, _x__EL_U_128;
float _diverge_delta, _x__diverge_delta;
float delta, _x_delta;
bool _EL_U_130, _x__EL_U_130;
bool _EL_U_132, _x__EL_U_132;
float v, _x_v;
float h, _x_h;
bool _EL_U_134, _x__EL_U_134;
bool _J174, _x__J174;
bool _J168, _x__J168;
bool _J162, _x__J162;
bool _J156, _x__J156;

  int __steps_to_fair = __VERIFIER_nondet_int();
  _EL_U_128 = __VERIFIER_nondet_bool();
  _diverge_delta = __VERIFIER_nondet_float();
  delta = __VERIFIER_nondet_float();
  _EL_U_130 = __VERIFIER_nondet_bool();
  _EL_U_132 = __VERIFIER_nondet_bool();
  v = __VERIFIER_nondet_float();
  h = __VERIFIER_nondet_float();
  _EL_U_134 = __VERIFIER_nondet_bool();
  _J174 = __VERIFIER_nondet_bool();
  _J168 = __VERIFIER_nondet_bool();
  _J162 = __VERIFIER_nondet_bool();
  _J156 = __VERIFIER_nondet_bool();

  bool __ok = ((((((h == 0.0) && (v == (981.0/100.0))) && ((delta == 0.0) || ( !((h == 0.0) && ( !(0.0 <= v)))))) && (0.0 <= delta)) && (delta == _diverge_delta)) && ((((( !(( !(_EL_U_134 || ( !(( !((h == 0.0) && (v == 0.0))) || _EL_U_132)))) || (_EL_U_130 || ( !((1.0 <= _diverge_delta) || _EL_U_128))))) && ( !_J156)) && ( !_J162)) && ( !_J168)) && ( !_J174)));
  while (__steps_to_fair >= 0 && __ok) {
    if ((((_J156 && _J162) && _J168) && _J174)) {
      __steps_to_fair = __VERIFIER_nondet_int();
    } else {
      __steps_to_fair--;
    }
    _x__EL_U_128 = __VERIFIER_nondet_bool();
    _x__diverge_delta = __VERIFIER_nondet_float();
    _x_delta = __VERIFIER_nondet_float();
    _x__EL_U_130 = __VERIFIER_nondet_bool();
    _x__EL_U_132 = __VERIFIER_nondet_bool();
    _x_v = __VERIFIER_nondet_float();
    _x_h = __VERIFIER_nondet_float();
    _x__EL_U_134 = __VERIFIER_nondet_bool();
    _x__J174 = __VERIFIER_nondet_bool();
    _x__J168 = __VERIFIER_nondet_bool();
    _x__J162 = __VERIFIER_nondet_bool();
    _x__J156 = __VERIFIER_nondet_bool();

    __ok = ((((((((_x_delta == 0.0) || ( !((_x_h == 0.0) && ( !(0.0 <= _x_v))))) && (0.0 <= _x_delta)) && (0.0 <= _x_h)) && (((_x_h == 0.0) || ( !((h == 0.0) && (v <= 0.0)))) && (((h == 0.0) && (v <= 0.0)) || (((200.0 * h) + ((-200.0 * _x_h) + ((-981.0 * (delta * delta)) + (200.0 * (v * delta))))) == 0.0)))) && ((((_x_v == 0.0) || ( !((h == 0.0) && ((v <= 0.0) && (-1.0 <= v))))) && (((v + _x_v) == -1.0) || ( !((h == 0.0) && ( !(-1.0 <= v)))))) && ((((100.0 * v) + ((-100.0 * _x_v) + (-981.0 * delta))) == 0.0) || ( !(( !(h <= 0.0)) || ( !(v <= 0.0))))))) && (((delta == _x__diverge_delta) || ( !(1.0 <= _diverge_delta))) && ((1.0 <= _diverge_delta) || ((delta + (_diverge_delta + (-1.0 * _x__diverge_delta))) == 0.0)))) && ((((((_EL_U_130 == (_x__EL_U_130 || ( !(_x__EL_U_128 || (1.0 <= _x__diverge_delta))))) && ((_EL_U_128 == (_x__EL_U_128 || (1.0 <= _x__diverge_delta))) && ((_EL_U_132 == (_x__EL_U_132 || ( !((_x_h == 0.0) && (_x_v == 0.0))))) && (_EL_U_134 == (_x__EL_U_134 || ( !(_x__EL_U_132 || ( !((_x_h == 0.0) && (_x_v == 0.0)))))))))) && (_x__J156 == (( !(((_J156 && _J162) && _J168) && _J174)) && ((((_J156 && _J162) && _J168) && _J174) || ((( !((h == 0.0) && (v == 0.0))) || ( !(( !((h == 0.0) && (v == 0.0))) || _EL_U_132))) || _J156))))) && (_x__J162 == (( !(((_J156 && _J162) && _J168) && _J174)) && ((((_J156 && _J162) && _J168) && _J174) || ((( !(( !((h == 0.0) && (v == 0.0))) || _EL_U_132)) || ( !(_EL_U_134 || ( !(( !((h == 0.0) && (v == 0.0))) || _EL_U_132))))) || _J162))))) && (_x__J168 == (( !(((_J156 && _J162) && _J168) && _J174)) && ((((_J156 && _J162) && _J168) && _J174) || (((1.0 <= _diverge_delta) || ( !((1.0 <= _diverge_delta) || _EL_U_128))) || _J168))))) && (_x__J174 == (( !(((_J156 && _J162) && _J168) && _J174)) && ((((_J156 && _J162) && _J168) && _J174) || ((( !((1.0 <= _diverge_delta) || _EL_U_128)) || ( !(_EL_U_130 || ( !((1.0 <= _diverge_delta) || _EL_U_128))))) || _J174))))));
    _EL_U_128 = _x__EL_U_128;
    _diverge_delta = _x__diverge_delta;
    delta = _x_delta;
    _EL_U_130 = _x__EL_U_130;
    _EL_U_132 = _x__EL_U_132;
    v = _x_v;
    h = _x_h;
    _EL_U_134 = _x__EL_U_134;
    _J174 = _x__J174;
    _J168 = _x__J168;
    _J162 = _x__J162;
    _J156 = _x__J156;

  }
}
