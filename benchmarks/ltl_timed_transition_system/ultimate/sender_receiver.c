//@ ltl invariant negative: ( ( ([] ( AP(s_l) || (<> AP(s_l)))) || (! ([] (<> AP(s_evt))))) || (! ([] (<> AP((1.0 <= _diverge_delta))))));
extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);
typedef enum {false, true} bool;
bool __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}

bool __ok;
float _diverge_delta, _x__diverge_delta;
float delta, _x_delta;
int r2s, _x_r2s;
bool r_l, _x_r_l;
float s_timeout, _x_s_timeout;
float s_c, _x_s_c;
int s2r, _x_s2r;
bool s_l, _x_s_l;
int s_msg_id, _x_s_msg_id;
bool s_evt, _x_s_evt;

int main()
{
  _diverge_delta = __VERIFIER_nondet_float();
  delta = __VERIFIER_nondet_float();
  r2s = __VERIFIER_nondet_int();
  r_l = __VERIFIER_nondet_bool();
  s_timeout = __VERIFIER_nondet_float();
  s_c = __VERIFIER_nondet_float();
  s2r = __VERIFIER_nondet_int();
  s_l = __VERIFIER_nondet_bool();
  s_msg_id = __VERIFIER_nondet_int();
  s_evt = __VERIFIER_nondet_bool();

  __ok = ((((((s_l && (s_c == 0.0)) && (s_msg_id == 0)) && (s_l || (s_c <= s_timeout))) && r_l) && (0.0 <= delta)) && (delta == _diverge_delta));
  while (__ok) {
    _x__diverge_delta = __VERIFIER_nondet_float();
    _x_delta = __VERIFIER_nondet_float();
    _x_r2s = __VERIFIER_nondet_int();
    _x_r_l = __VERIFIER_nondet_bool();
    _x_s_timeout = __VERIFIER_nondet_float();
    _x_s_c = __VERIFIER_nondet_float();
    _x_s2r = __VERIFIER_nondet_int();
    _x_s_l = __VERIFIER_nondet_bool();
    _x_s_msg_id = __VERIFIER_nondet_int();
    _x_s_evt = __VERIFIER_nondet_bool();

    __ok = ((((((((((((_x_s_l || (_x_s_c <= _x_s_timeout)) && (((((s_l == _x_s_l) && (s_msg_id == _x_s_msg_id)) && ((s_timeout == _x_s_timeout) && ((delta + (s_c + (-1.0 * _x_s_c))) == 0.0))) && (s2r == _x_s2r)) || ( !(( !s_evt) || ( !(delta <= 0.0)))))) && ((((s_msg_id == _x_s_msg_id) && (_x_s_timeout == 1.0)) && ((s2r == _x_s2r) && (_x_s_c == 0.0))) || ( !((s_evt && (delta == 0.0)) && (s_l && _x_s_l))))) && ((((s2r == _x_s2r) && (_x_s_c == 0.0)) && ((_x_s_timeout == 1.0) && ((s_msg_id + (-1 * _x_s_msg_id)) == -1))) || ( !((s_evt && (delta == 0.0)) && (s_l && ( !_x_s_l)))))) && ((((s2r == _x_s2r) && (_x_s_c == 0.0)) && (( !_x_s_l) == (( !(r2s == s_msg_id)) && (s_timeout <= s_c)))) || ( !(( !s_l) && (s_evt && (delta == 0.0)))))) && (( !(_x_s_timeout <= s_timeout)) || ( !((s_evt && (delta == 0.0)) && (( !s_l) && ( !_x_s_l)))))) && (( !(( !s_l) && (s_evt && (delta == 0.0)))) || (_x_s_l == ((r2s == s_msg_id) && ( !(s_timeout <= s_c)))))) && ((_x_s_timeout == 1.0) || ( !((s_evt && (delta == 0.0)) && (_x_s_l && ( !s_l)))))) && ((((((delta <= 0.0) || ((r_l == _x_r_l) && (r2s == _x_r2s))) && ((_x_r_l == (r2s == s2r)) || ( !((delta == 0.0) && r_l)))) && ((r2s == _x_r2s) || ( !((delta == 0.0) && (r_l && _x_r_l))))) && ((_x_r2s == s2r) || ( !((delta == 0.0) && (r_l && ( !_x_r_l)))))) && ((r2s == _x_r2s) || ( !((delta == 0.0) && ( !r_l)))))) && (0.0 <= _x_delta)) && ((delta <= 0.0) || ((s2r == _x_s2r) && (r2s == _x_r2s)))) && (((delta == _x__diverge_delta) || ( !(1.0 <= _diverge_delta))) && ((1.0 <= _diverge_delta) || ((delta + (_diverge_delta + (-1.0 * _x__diverge_delta))) == 0.0))));
    _diverge_delta = _x__diverge_delta;
    delta = _x_delta;
    r2s = _x_r2s;
    r_l = _x_r_l;
    s_timeout = _x_s_timeout;
    s_c = _x_s_c;
    s2r = _x_s2r;
    s_l = _x_s_l;
    s_msg_id = _x_s_msg_id;
    s_evt = _x_s_evt;

  }
}
