extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);
typedef enum {false, true} bool;
bool __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}

int main()
{
bool _EL_U_85, _x__EL_U_85;
float bound, _x_bound;
float _diverge_delta, _x__diverge_delta;
float delta, _x_delta;
int counter, _x_counter;
float c, _x_c;
bool _EL_U_87, _x__EL_U_87;
bool _J130, _x__J130;
bool _J124, _x__J124;
bool _J118, _x__J118;
bool _J112, _x__J112;
bool _EL_U_80, _x__EL_U_80;
bool _EL_U_82, _x__EL_U_82;

  int __steps_to_fair = __VERIFIER_nondet_int();
  _EL_U_85 = __VERIFIER_nondet_bool();
  bound = __VERIFIER_nondet_float();
  _diverge_delta = __VERIFIER_nondet_float();
  delta = __VERIFIER_nondet_float();
  counter = __VERIFIER_nondet_int();
  c = __VERIFIER_nondet_float();
  _EL_U_87 = __VERIFIER_nondet_bool();
  _J130 = __VERIFIER_nondet_bool();
  _J124 = __VERIFIER_nondet_bool();
  _J118 = __VERIFIER_nondet_bool();
  _J112 = __VERIFIER_nondet_bool();
  _EL_U_80 = __VERIFIER_nondet_bool();
  _EL_U_82 = __VERIFIER_nondet_bool();

  bool __ok = ((((0.0 <= delta) && ((c == 0.0) && (counter == 0))) && (delta == _diverge_delta)) && ((((( !((_EL_U_87 || ( !(( !(( !(delta <= 0.0)) || ( !(c == bound)))) || _EL_U_85))) || (_EL_U_82 || ( !((1.0 <= _diverge_delta) || _EL_U_80))))) && ( !_J112)) && ( !_J118)) && ( !_J124)) && ( !_J130)));
  while (__steps_to_fair >= 0 && __ok) {
    if ((((_J112 && _J118) && _J124) && _J130)) {
      __steps_to_fair = __VERIFIER_nondet_int();
    } else {
      __steps_to_fair--;
    }
    _x__EL_U_85 = __VERIFIER_nondet_bool();
    _x_bound = __VERIFIER_nondet_float();
    _x__diverge_delta = __VERIFIER_nondet_float();
    _x_delta = __VERIFIER_nondet_float();
    _x_counter = __VERIFIER_nondet_int();
    _x_c = __VERIFIER_nondet_float();
    _x__EL_U_87 = __VERIFIER_nondet_bool();
    _x__J130 = __VERIFIER_nondet_bool();
    _x__J124 = __VERIFIER_nondet_bool();
    _x__J118 = __VERIFIER_nondet_bool();
    _x__J112 = __VERIFIER_nondet_bool();
    _x__EL_U_80 = __VERIFIER_nondet_bool();
    _x__EL_U_82 = __VERIFIER_nondet_bool();

    __ok = ((((((0.0 <= _x_delta) && ((delta <= 0.0) || (((c + ((-1.0 * _x_c) + delta)) == 0.0) && (counter == _x_counter)))) && ((((counter + (-1 * _x_counter)) == -1) && (_x_c == ((float)((counter * counter))))) || ( !((delta == 0.0) && (c == bound))))) && (((counter == _x_counter) && (c == _x_c)) || ( !((delta == 0.0) && ( !(c == bound)))))) && (((delta == _x__diverge_delta) || ( !(1.0 <= _diverge_delta))) && ((1.0 <= _diverge_delta) || ((delta + (_diverge_delta + (-1.0 * _x__diverge_delta))) == 0.0)))) && ((((((_EL_U_82 == (_x__EL_U_82 || ( !(_x__EL_U_80 || (1.0 <= _x__diverge_delta))))) && ((_EL_U_80 == (_x__EL_U_80 || (1.0 <= _x__diverge_delta))) && ((_EL_U_85 == (_x__EL_U_85 || ( !(( !(_x_c == _x_bound)) || ( !(_x_delta <= 0.0)))))) && (_EL_U_87 == (_x__EL_U_87 || ( !(_x__EL_U_85 || ( !(( !(_x_c == _x_bound)) || ( !(_x_delta <= 0.0))))))))))) && (_x__J112 == (( !(((_J112 && _J118) && _J124) && _J130)) && ((((_J112 && _J118) && _J124) && _J130) || ((( !(( !(delta <= 0.0)) || ( !(c == bound)))) || ( !(( !(( !(delta <= 0.0)) || ( !(c == bound)))) || _EL_U_85))) || _J112))))) && (_x__J118 == (( !(((_J112 && _J118) && _J124) && _J130)) && ((((_J112 && _J118) && _J124) && _J130) || ((( !(( !(( !(delta <= 0.0)) || ( !(c == bound)))) || _EL_U_85)) || ( !(_EL_U_87 || ( !(( !(( !(delta <= 0.0)) || ( !(c == bound)))) || _EL_U_85))))) || _J118))))) && (_x__J124 == (( !(((_J112 && _J118) && _J124) && _J130)) && ((((_J112 && _J118) && _J124) && _J130) || (((1.0 <= _diverge_delta) || ( !((1.0 <= _diverge_delta) || _EL_U_80))) || _J124))))) && (_x__J130 == (( !(((_J112 && _J118) && _J124) && _J130)) && ((((_J112 && _J118) && _J124) && _J130) || ((( !((1.0 <= _diverge_delta) || _EL_U_80)) || ( !(_EL_U_82 || ( !((1.0 <= _diverge_delta) || _EL_U_80))))) || _J130))))));
    _EL_U_85 = _x__EL_U_85;
    bound = _x_bound;
    _diverge_delta = _x__diverge_delta;
    delta = _x_delta;
    counter = _x_counter;
    c = _x_c;
    _EL_U_87 = _x__EL_U_87;
    _J130 = _x__J130;
    _J124 = _x__J124;
    _J118 = _x__J118;
    _J112 = _x__J112;
    _EL_U_80 = _x__EL_U_80;
    _EL_U_82 = _x__EL_U_82;

  }
}
