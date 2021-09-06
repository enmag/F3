extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);
typedef enum {false, true} bool;
bool __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}

int main()
{
bool _EL_U_141, _x__EL_U_141;
float _diverge_delta, _x__diverge_delta;
float delta, _x_delta;
bool _EL_U_143, _x__EL_U_143;
float v, _x_v;
bool _EL_U_145, _x__EL_U_145;
float h, _x_h;
int counter, _x_counter;
bool _J185, _x__J185;
bool _J179, _x__J179;
bool _J173, _x__J173;
bool stop, _x_stop;
bool _J167, _x__J167;
bool _EL_U_139, _x__EL_U_139;

  int __steps_to_fair = __VERIFIER_nondet_int();
  _EL_U_141 = __VERIFIER_nondet_bool();
  _diverge_delta = __VERIFIER_nondet_float();
  delta = __VERIFIER_nondet_float();
  _EL_U_143 = __VERIFIER_nondet_bool();
  v = __VERIFIER_nondet_float();
  _EL_U_145 = __VERIFIER_nondet_bool();
  h = __VERIFIER_nondet_float();
  counter = __VERIFIER_nondet_int();
  _J185 = __VERIFIER_nondet_bool();
  _J179 = __VERIFIER_nondet_bool();
  _J173 = __VERIFIER_nondet_bool();
  stop = __VERIFIER_nondet_bool();
  _J167 = __VERIFIER_nondet_bool();
  _EL_U_139 = __VERIFIER_nondet_bool();

  bool __ok = (((((counter == 1) && (h == 0.0)) && ((v == (981.0/200.0)) && (0.0 <= delta))) && (delta == _diverge_delta)) && ((((( !((_EL_U_145 || ( !(((h == 0.0) && ( !(v <= 0.0))) || _EL_U_143))) || (_EL_U_141 || ( !((1.0 <= _diverge_delta) || _EL_U_139))))) && ( !_J167)) && ( !_J173)) && ( !_J179)) && ( !_J185)));
  while (__steps_to_fair >= 0 && __ok) {
    if ((((_J167 && _J173) && _J179) && _J185)) {
      __steps_to_fair = __VERIFIER_nondet_int();
    } else {
      __steps_to_fair--;
    }
    _x__EL_U_141 = __VERIFIER_nondet_bool();
    _x__diverge_delta = __VERIFIER_nondet_float();
    _x_delta = __VERIFIER_nondet_float();
    _x__EL_U_143 = __VERIFIER_nondet_bool();
    _x_v = __VERIFIER_nondet_float();
    _x__EL_U_145 = __VERIFIER_nondet_bool();
    _x_h = __VERIFIER_nondet_float();
    _x_counter = __VERIFIER_nondet_int();
    _x__J185 = __VERIFIER_nondet_bool();
    _x__J179 = __VERIFIER_nondet_bool();
    _x__J173 = __VERIFIER_nondet_bool();
    _x_stop = __VERIFIER_nondet_bool();
    _x__J167 = __VERIFIER_nondet_bool();
    _x__EL_U_139 = __VERIFIER_nondet_bool();

    __ok = (((((((((counter + (-1 * _x_counter)) == -1) || ( !((h == 0.0) && ( !(0.0 <= v))))) && (((h == 0.0) && ( !(0.0 <= v))) || (counter == _x_counter))) && (((_x_h == 0.0) || ( !((h == 0.0) && (stop || (v <= 0.0))))) && (((h == 0.0) && (stop || (v <= 0.0))) || (((200.0 * h) + ((-200.0 * _x_h) + ((200.0 * (v * delta)) + (-981.0 * (delta * delta))))) == 0.0)))) && (((_x_v == 0.0) || ( !(stop && (h == 0.0)))) && ((((_x_v + ((v * ((float)(counter))) / ((float)((counter + 1))))) == 0.0) || ( !(( !stop) && ((h == 0.0) && (v <= 0.0))))) && (((stop && (h == 0.0)) || (( !stop) && ((h == 0.0) && (v <= 0.0)))) || (((100.0 * v) + ((-100.0 * _x_v) + (-981.0 * delta))) == 0.0))))) && (((0.0 <= _x_h) && (0.0 <= _x_delta)) && ((_x_delta == 0.0) || ( !((_x_h == 0.0) && ( !(0.0 <= _x_v))))))) && (((delta == _x__diverge_delta) || ( !(1.0 <= _diverge_delta))) && ((1.0 <= _diverge_delta) || ((delta + (_diverge_delta + (-1.0 * _x__diverge_delta))) == 0.0)))) && ((((((_EL_U_141 == (_x__EL_U_141 || ( !(_x__EL_U_139 || (1.0 <= _x__diverge_delta))))) && ((_EL_U_139 == (_x__EL_U_139 || (1.0 <= _x__diverge_delta))) && ((_EL_U_143 == (_x__EL_U_143 || ((_x_h == 0.0) && ( !(_x_v <= 0.0))))) && (_EL_U_145 == (_x__EL_U_145 || ( !(_x__EL_U_143 || ((_x_h == 0.0) && ( !(_x_v <= 0.0)))))))))) && (_x__J167 == (( !(((_J167 && _J173) && _J179) && _J185)) && ((((_J167 && _J173) && _J179) && _J185) || ((((h == 0.0) && ( !(v <= 0.0))) || ( !(((h == 0.0) && ( !(v <= 0.0))) || _EL_U_143))) || _J167))))) && (_x__J173 == (( !(((_J167 && _J173) && _J179) && _J185)) && ((((_J167 && _J173) && _J179) && _J185) || ((( !(((h == 0.0) && ( !(v <= 0.0))) || _EL_U_143)) || ( !(_EL_U_145 || ( !(((h == 0.0) && ( !(v <= 0.0))) || _EL_U_143))))) || _J173))))) && (_x__J179 == (( !(((_J167 && _J173) && _J179) && _J185)) && ((((_J167 && _J173) && _J179) && _J185) || (((1.0 <= _diverge_delta) || ( !((1.0 <= _diverge_delta) || _EL_U_139))) || _J179))))) && (_x__J185 == (( !(((_J167 && _J173) && _J179) && _J185)) && ((((_J167 && _J173) && _J179) && _J185) || ((( !((1.0 <= _diverge_delta) || _EL_U_139)) || ( !(_EL_U_141 || ( !((1.0 <= _diverge_delta) || _EL_U_139))))) || _J185))))));
    _EL_U_141 = _x__EL_U_141;
    _diverge_delta = _x__diverge_delta;
    delta = _x_delta;
    _EL_U_143 = _x__EL_U_143;
    v = _x_v;
    _EL_U_145 = _x__EL_U_145;
    h = _x_h;
    counter = _x_counter;
    _J185 = _x__J185;
    _J179 = _x__J179;
    _J173 = _x__J173;
    stop = _x_stop;
    _J167 = _x__J167;
    _EL_U_139 = _x__EL_U_139;

  }
}
