extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);
typedef enum {false, true} bool;
bool __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}

int main()
{
bool _EL_U_128, _x__EL_U_128;
bool _EL_U_130, _x__EL_U_130;
float _diverge_delta, _x__diverge_delta;
float delta, _x_delta;
float v, _x_v;
bool _EL_U_132, _x__EL_U_132;
float h, _x_h;
bool stop, _x_stop;
int counter, _x_counter;
bool _J172, _x__J172;
bool _J166, _x__J166;
bool _J160, _x__J160;
bool _J154, _x__J154;
bool _EL_U_126, _x__EL_U_126;

  int __steps_to_fair = __VERIFIER_nondet_int();
  _EL_U_128 = __VERIFIER_nondet_bool();
  _EL_U_130 = __VERIFIER_nondet_bool();
  _diverge_delta = __VERIFIER_nondet_float();
  delta = __VERIFIER_nondet_float();
  v = __VERIFIER_nondet_float();
  _EL_U_132 = __VERIFIER_nondet_bool();
  h = __VERIFIER_nondet_float();
  stop = __VERIFIER_nondet_bool();
  counter = __VERIFIER_nondet_int();
  _J172 = __VERIFIER_nondet_bool();
  _J166 = __VERIFIER_nondet_bool();
  _J160 = __VERIFIER_nondet_bool();
  _J154 = __VERIFIER_nondet_bool();
  _EL_U_126 = __VERIFIER_nondet_bool();

  bool __ok = (((((counter == 1) && (h == 0.0)) && (v == (981.0/200.0))) && (delta == _diverge_delta)) && ((((( !((_EL_U_132 || ( !(((h == 0.0) && ( !(v <= 0.0))) || _EL_U_130))) || (_EL_U_128 || ( !((1.0 <= _diverge_delta) || _EL_U_126))))) && ( !_J154)) && ( !_J160)) && ( !_J166)) && ( !_J172)));
  while (__steps_to_fair >= 0 && __ok) {
    if ((((_J154 && _J160) && _J166) && _J172)) {
      __steps_to_fair = __VERIFIER_nondet_int();
    } else {
      __steps_to_fair--;
    }
    _x__EL_U_128 = __VERIFIER_nondet_bool();
    _x__EL_U_130 = __VERIFIER_nondet_bool();
    _x__diverge_delta = __VERIFIER_nondet_float();
    _x_delta = __VERIFIER_nondet_float();
    _x_v = __VERIFIER_nondet_float();
    _x__EL_U_132 = __VERIFIER_nondet_bool();
    _x_h = __VERIFIER_nondet_float();
    _x_stop = __VERIFIER_nondet_bool();
    _x_counter = __VERIFIER_nondet_int();
    _x__J172 = __VERIFIER_nondet_bool();
    _x__J166 = __VERIFIER_nondet_bool();
    _x__J160 = __VERIFIER_nondet_bool();
    _x__J154 = __VERIFIER_nondet_bool();
    _x__EL_U_126 = __VERIFIER_nondet_bool();

    __ok = ((((((((counter + (-1 * _x_counter)) == -1) || ( !((h == 0.0) && ( !(0.0 <= v))))) && (((h == 0.0) && ( !(0.0 <= v))) || (counter == _x_counter))) && (((_x_h == 0.0) || ( !((h == 0.0) && (stop || (v <= 0.0))))) && (((h == 0.0) && (stop || (v <= 0.0))) || (((200.0 * h) + ((-200.0 * _x_h) + ((200.0 * (v * delta)) + (-981.0 * (delta * delta))))) == 0.0)))) && (((_x_v == 0.0) || ( !(stop && (h == 0.0)))) && ((((_x_v + ((v * ((float)(counter))) / ((float)((counter + 1))))) == 0.0) || ( !(( !stop) && ((h == 0.0) && (v <= 0.0))))) && (((stop && (h == 0.0)) && (( !stop) && ((h == 0.0) && (v <= 0.0)))) || (((100.0 * v) + ((-100.0 * _x_v) + (-981.0 * delta))) == 0.0))))) && (((delta == _x__diverge_delta) || ( !(1.0 <= _diverge_delta))) && ((1.0 <= _diverge_delta) || ((delta + (_diverge_delta + (-1.0 * _x__diverge_delta))) == 0.0)))) && ((((((_EL_U_128 == (_x__EL_U_128 || ( !(_x__EL_U_126 || (1.0 <= _x__diverge_delta))))) && ((_EL_U_126 == (_x__EL_U_126 || (1.0 <= _x__diverge_delta))) && ((_EL_U_130 == (_x__EL_U_130 || ((_x_h == 0.0) && ( !(_x_v <= 0.0))))) && (_EL_U_132 == (_x__EL_U_132 || ( !(_x__EL_U_130 || ((_x_h == 0.0) && ( !(_x_v <= 0.0)))))))))) && (_x__J154 == (( !(((_J154 && _J160) && _J166) && _J172)) && ((((_J154 && _J160) && _J166) && _J172) || ((((h == 0.0) && ( !(v <= 0.0))) || ( !(((h == 0.0) && ( !(v <= 0.0))) || _EL_U_130))) || _J154))))) && (_x__J160 == (( !(((_J154 && _J160) && _J166) && _J172)) && ((((_J154 && _J160) && _J166) && _J172) || ((( !(((h == 0.0) && ( !(v <= 0.0))) || _EL_U_130)) || ( !(_EL_U_132 || ( !(((h == 0.0) && ( !(v <= 0.0))) || _EL_U_130))))) || _J160))))) && (_x__J166 == (( !(((_J154 && _J160) && _J166) && _J172)) && ((((_J154 && _J160) && _J166) && _J172) || (((1.0 <= _diverge_delta) || ( !((1.0 <= _diverge_delta) || _EL_U_126))) || _J166))))) && (_x__J172 == (( !(((_J154 && _J160) && _J166) && _J172)) && ((((_J154 && _J160) && _J166) && _J172) || ((( !((1.0 <= _diverge_delta) || _EL_U_126)) || ( !(_EL_U_128 || ( !((1.0 <= _diverge_delta) || _EL_U_126))))) || _J172))))));
    _EL_U_128 = _x__EL_U_128;
    _EL_U_130 = _x__EL_U_130;
    _diverge_delta = _x__diverge_delta;
    delta = _x_delta;
    v = _x_v;
    _EL_U_132 = _x__EL_U_132;
    h = _x_h;
    stop = _x_stop;
    counter = _x_counter;
    _J172 = _x__J172;
    _J166 = _x__J166;
    _J160 = _x__J160;
    _J154 = _x__J154;
    _EL_U_126 = _x__EL_U_126;

  }
}
