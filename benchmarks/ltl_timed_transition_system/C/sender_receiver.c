extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);
typedef enum {false, true} bool;
bool __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}

int main()
{
float _diverge_delta, _x__diverge_delta;
float delta, _x_delta;
bool r_l, _x_r_l;
float s_timeout, _x_s_timeout;
float s_c, _x_s_c;
bool s_l, _x_s_l;
int s_msg_id, _x_s_msg_id;
bool _J246, _x__J246;
bool _J240, _x__J240;
bool _J233, _x__J233;
bool _J227, _x__J227;
bool _J222, _x__J222;
bool _J213, _x__J213;
bool _EL_U_175, _x__EL_U_175;
bool _EL_U_177, _x__EL_U_177;
bool _EL_U_179, _x__EL_U_179;
bool s_evt, _x_s_evt;
bool _EL_U_181, _x__EL_U_181;
bool _EL_U_183, _x__EL_U_183;
bool _EL_U_186, _x__EL_U_186;
int r2s, _x_r2s;
int s2r, _x_s2r;

  int __steps_to_fair = __VERIFIER_nondet_int();
  _diverge_delta = __VERIFIER_nondet_float();
  delta = __VERIFIER_nondet_float();
  r_l = __VERIFIER_nondet_bool();
  s_timeout = __VERIFIER_nondet_float();
  s_c = __VERIFIER_nondet_float();
  s_l = __VERIFIER_nondet_bool();
  s_msg_id = __VERIFIER_nondet_int();
  _J246 = __VERIFIER_nondet_bool();
  _J240 = __VERIFIER_nondet_bool();
  _J233 = __VERIFIER_nondet_bool();
  _J227 = __VERIFIER_nondet_bool();
  _J222 = __VERIFIER_nondet_bool();
  _J213 = __VERIFIER_nondet_bool();
  _EL_U_175 = __VERIFIER_nondet_bool();
  _EL_U_177 = __VERIFIER_nondet_bool();
  _EL_U_179 = __VERIFIER_nondet_bool();
  s_evt = __VERIFIER_nondet_bool();
  _EL_U_181 = __VERIFIER_nondet_bool();
  _EL_U_183 = __VERIFIER_nondet_bool();
  _EL_U_186 = __VERIFIER_nondet_bool();
  r2s = __VERIFIER_nondet_int();
  s2r = __VERIFIER_nondet_int();

  bool __ok = (((((((s_l && (s_c == 0.0)) && (s_msg_id == 0)) && (s_l || (s_c <= s_timeout))) && r_l) && (0.0 <= delta)) && (delta == _diverge_delta)) && ((((((( !((( !(_EL_U_186 || ( !(s_l || (s_l || _EL_U_183))))) || (_EL_U_181 || ( !(s_evt || _EL_U_179)))) || (_EL_U_177 || ( !((1.0 <= _diverge_delta) || _EL_U_175))))) && ( !_J213)) && ( !_J222)) && ( !_J227)) && ( !_J233)) && ( !_J240)) && ( !_J246)));
  while (__steps_to_fair >= 0 && __ok) {
    if ((((((_J213 && _J222) && _J227) && _J233) && _J240) && _J246)) {
      __steps_to_fair = __VERIFIER_nondet_int();
    } else {
      __steps_to_fair--;
    }
    _x__diverge_delta = __VERIFIER_nondet_float();
    _x_delta = __VERIFIER_nondet_float();
    _x_r_l = __VERIFIER_nondet_bool();
    _x_s_timeout = __VERIFIER_nondet_float();
    _x_s_c = __VERIFIER_nondet_float();
    _x_s_l = __VERIFIER_nondet_bool();
    _x_s_msg_id = __VERIFIER_nondet_int();
    _x__J246 = __VERIFIER_nondet_bool();
    _x__J240 = __VERIFIER_nondet_bool();
    _x__J233 = __VERIFIER_nondet_bool();
    _x__J227 = __VERIFIER_nondet_bool();
    _x__J222 = __VERIFIER_nondet_bool();
    _x__J213 = __VERIFIER_nondet_bool();
    _x__EL_U_175 = __VERIFIER_nondet_bool();
    _x__EL_U_177 = __VERIFIER_nondet_bool();
    _x__EL_U_179 = __VERIFIER_nondet_bool();
    _x_s_evt = __VERIFIER_nondet_bool();
    _x__EL_U_181 = __VERIFIER_nondet_bool();
    _x__EL_U_183 = __VERIFIER_nondet_bool();
    _x__EL_U_186 = __VERIFIER_nondet_bool();
    _x_r2s = __VERIFIER_nondet_int();
    _x_s2r = __VERIFIER_nondet_int();

    __ok = (((((((((((((_x_s_l || (_x_s_c <= _x_s_timeout)) && (((((s_l == _x_s_l) && (s_msg_id == _x_s_msg_id)) && ((s_timeout == _x_s_timeout) && ((delta + (s_c + (-1.0 * _x_s_c))) == 0.0))) && (s2r == _x_s2r)) || ( !(( !s_evt) || ( !(delta <= 0.0)))))) && ((((s_msg_id == _x_s_msg_id) && (_x_s_timeout == 1.0)) && ((s2r == _x_s2r) && (_x_s_c == 0.0))) || ( !((s_evt && (delta == 0.0)) && (s_l && _x_s_l))))) && ((((s2r == _x_s2r) && (_x_s_c == 0.0)) && ((_x_s_timeout == 1.0) && ((s_msg_id + (-1 * _x_s_msg_id)) == -1))) || ( !((s_evt && (delta == 0.0)) && (s_l && ( !_x_s_l)))))) && ((((s2r == _x_s2r) && (_x_s_c == 0.0)) && (( !_x_s_l) == (( !(r2s == s_msg_id)) && (s_timeout <= s_c)))) || ( !(( !s_l) && (s_evt && (delta == 0.0)))))) && (( !(_x_s_timeout <= s_timeout)) || ( !((s_evt && (delta == 0.0)) && (( !s_l) && ( !_x_s_l)))))) && (( !(( !s_l) && (s_evt && (delta == 0.0)))) || (_x_s_l == ((r2s == s_msg_id) && ( !(s_timeout <= s_c)))))) && ((_x_s_timeout == 1.0) || ( !((s_evt && (delta == 0.0)) && (_x_s_l && ( !s_l)))))) && ((((((delta <= 0.0) || ((r_l == _x_r_l) && (r2s == _x_r2s))) && ((_x_r_l == (r2s == s2r)) || ( !((delta == 0.0) && r_l)))) && ((r2s == _x_r2s) || ( !((delta == 0.0) && (r_l && _x_r_l))))) && ((_x_r2s == s2r) || ( !((delta == 0.0) && (r_l && ( !_x_r_l)))))) && ((r2s == _x_r2s) || ( !((delta == 0.0) && ( !r_l)))))) && (0.0 <= _x_delta)) && ((delta <= 0.0) || ((s2r == _x_s2r) && (r2s == _x_r2s)))) && (((delta == _x__diverge_delta) || ( !(1.0 <= _diverge_delta))) && ((1.0 <= _diverge_delta) || ((delta + (_diverge_delta + (-1.0 * _x__diverge_delta))) == 0.0)))) && ((((((((_EL_U_177 == (_x__EL_U_177 || ( !(_x__EL_U_175 || (1.0 <= _x__diverge_delta))))) && ((_EL_U_175 == (_x__EL_U_175 || (1.0 <= _x__diverge_delta))) && ((_EL_U_181 == (_x__EL_U_181 || ( !(_x_s_evt || _x__EL_U_179)))) && ((_EL_U_179 == (_x_s_evt || _x__EL_U_179)) && ((_EL_U_183 == (_x_s_l || _x__EL_U_183)) && (_EL_U_186 == (_x__EL_U_186 || ( !(_x_s_l || (_x_s_l || _x__EL_U_183)))))))))) && (_x__J213 == (( !(((((_J213 && _J222) && _J227) && _J233) && _J240) && _J246)) && ((((((_J213 && _J222) && _J227) && _J233) && _J240) && _J246) || ((s_l || ( !(s_l || _EL_U_183))) || _J213))))) && (_x__J222 == (( !(((((_J213 && _J222) && _J227) && _J233) && _J240) && _J246)) && ((((((_J213 && _J222) && _J227) && _J233) && _J240) && _J246) || ((( !(s_l || (s_l || _EL_U_183))) || ( !(_EL_U_186 || ( !(s_l || (s_l || _EL_U_183)))))) || _J222))))) && (_x__J227 == (( !(((((_J213 && _J222) && _J227) && _J233) && _J240) && _J246)) && ((((((_J213 && _J222) && _J227) && _J233) && _J240) && _J246) || ((s_evt || ( !(s_evt || _EL_U_179))) || _J227))))) && (_x__J233 == (( !(((((_J213 && _J222) && _J227) && _J233) && _J240) && _J246)) && ((((((_J213 && _J222) && _J227) && _J233) && _J240) && _J246) || ((( !(s_evt || _EL_U_179)) || ( !(_EL_U_181 || ( !(s_evt || _EL_U_179))))) || _J233))))) && (_x__J240 == (( !(((((_J213 && _J222) && _J227) && _J233) && _J240) && _J246)) && ((((((_J213 && _J222) && _J227) && _J233) && _J240) && _J246) || (((1.0 <= _diverge_delta) || ( !((1.0 <= _diverge_delta) || _EL_U_175))) || _J240))))) && (_x__J246 == (( !(((((_J213 && _J222) && _J227) && _J233) && _J240) && _J246)) && ((((((_J213 && _J222) && _J227) && _J233) && _J240) && _J246) || ((( !((1.0 <= _diverge_delta) || _EL_U_175)) || ( !(_EL_U_177 || ( !((1.0 <= _diverge_delta) || _EL_U_175))))) || _J246))))));
    _diverge_delta = _x__diverge_delta;
    delta = _x_delta;
    r_l = _x_r_l;
    s_timeout = _x_s_timeout;
    s_c = _x_s_c;
    s_l = _x_s_l;
    s_msg_id = _x_s_msg_id;
    _J246 = _x__J246;
    _J240 = _x__J240;
    _J233 = _x__J233;
    _J227 = _x__J227;
    _J222 = _x__J222;
    _J213 = _x__J213;
    _EL_U_175 = _x__EL_U_175;
    _EL_U_177 = _x__EL_U_177;
    _EL_U_179 = _x__EL_U_179;
    s_evt = _x_s_evt;
    _EL_U_181 = _x__EL_U_181;
    _EL_U_183 = _x__EL_U_183;
    _EL_U_186 = _x__EL_U_186;
    r2s = _x_r2s;
    s2r = _x_s2r;

  }
}
