//@ ltl invariant negative: ( ( ([] ( AP((s_l != 0)) || (<> AP((s_l != 0))))) || (! ([] (<> AP((s_evt != 0)))))) || (! ([] (<> AP((1.0 <= _diverge_delta))))));

extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);

char __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}


float _diverge_delta, _x__diverge_delta;
float s_c, _x_s_c;
float s_timeout, _x_s_timeout;
char r_l, _x_r_l;
int s_msg_id, _x_s_msg_id;
char s_evt, _x_s_evt;
char s_l, _x_s_l;
float delta, _x_delta;
int s2r, _x_s2r;
int r2s, _x_r2s;

int main()
{
  _diverge_delta = __VERIFIER_nondet_float();
  s_c = __VERIFIER_nondet_float();
  s_timeout = __VERIFIER_nondet_float();
  r_l = __VERIFIER_nondet_bool();
  s_msg_id = __VERIFIER_nondet_int();
  s_evt = __VERIFIER_nondet_bool();
  s_l = __VERIFIER_nondet_bool();
  delta = __VERIFIER_nondet_float();
  s2r = __VERIFIER_nondet_int();
  r2s = __VERIFIER_nondet_int();

  int __ok = (((((((s_l != 0) && (s_c == 0.0)) && (s_msg_id == 0)) && ((s_l != 0) || (s_c <= s_timeout))) && (r_l != 0)) && (0.0 <= delta)) && (delta == _diverge_delta));
  while (__ok) {
    _x__diverge_delta = __VERIFIER_nondet_float();
    _x_s_c = __VERIFIER_nondet_float();
    _x_s_timeout = __VERIFIER_nondet_float();
    _x_r_l = __VERIFIER_nondet_bool();
    _x_s_msg_id = __VERIFIER_nondet_int();
    _x_s_evt = __VERIFIER_nondet_bool();
    _x_s_l = __VERIFIER_nondet_bool();
    _x_delta = __VERIFIER_nondet_float();
    _x_s2r = __VERIFIER_nondet_int();
    _x_r2s = __VERIFIER_nondet_int();

    __ok = (((((((((((((_x_s_l != 0) || (_x_s_c <= _x_s_timeout)) && ((((((s_l != 0) == (_x_s_l != 0)) && (s_msg_id == _x_s_msg_id)) && ((s_timeout == _x_s_timeout) && ((delta + (s_c + (-1.0 * _x_s_c))) == 0.0))) && (s2r == _x_s2r)) || ( !(( !(s_evt != 0)) || ( !(delta <= 0.0)))))) && ((((s_msg_id == _x_s_msg_id) && (_x_s_timeout == 1.0)) && ((s2r == _x_s2r) && (_x_s_c == 0.0))) || ( !(((s_evt != 0) && (delta == 0.0)) && ((s_l != 0) && (_x_s_l != 0)))))) && ((((s2r == _x_s2r) && (_x_s_c == 0.0)) && ((_x_s_timeout == 1.0) && ((s_msg_id + (-1 * _x_s_msg_id)) == -1))) || ( !(((s_evt != 0) && (delta == 0.0)) && ((s_l != 0) && ( !(_x_s_l != 0))))))) && ((((s2r == _x_s2r) && (_x_s_c == 0.0)) && (( !(_x_s_l != 0)) == (( !(r2s == s_msg_id)) && (s_timeout <= s_c)))) || ( !(( !(s_l != 0)) && ((s_evt != 0) && (delta == 0.0)))))) && (( !(_x_s_timeout <= s_timeout)) || ( !(((s_evt != 0) && (delta == 0.0)) && (( !(s_l != 0)) && ( !(_x_s_l != 0))))))) && (( !(( !(s_l != 0)) && ((s_evt != 0) && (delta == 0.0)))) || ((_x_s_l != 0) == ((r2s == s_msg_id) && ( !(s_timeout <= s_c)))))) && ((_x_s_timeout == 1.0) || ( !(((s_evt != 0) && (delta == 0.0)) && ((_x_s_l != 0) && ( !(s_l != 0))))))) && ((((((delta <= 0.0) || (((r_l != 0) == (_x_r_l != 0)) && (r2s == _x_r2s))) && (((_x_r_l != 0) == (r2s == s2r)) || ( !((delta == 0.0) && (r_l != 0))))) && ((r2s == _x_r2s) || ( !((delta == 0.0) && ((r_l != 0) && (_x_r_l != 0)))))) && ((_x_r2s == s2r) || ( !((delta == 0.0) && ((r_l != 0) && ( !(_x_r_l != 0))))))) && ((r2s == _x_r2s) || ( !((delta == 0.0) && ( !(r_l != 0))))))) && (0.0 <= _x_delta)) && ((delta <= 0.0) || ((s2r == _x_s2r) && (r2s == _x_r2s)))) && (((delta == _x__diverge_delta) || ( !(1.0 <= _diverge_delta))) && ((1.0 <= _diverge_delta) || ((delta + (_diverge_delta + (-1.0 * _x__diverge_delta))) == 0.0))));
    _diverge_delta = _x__diverge_delta;
    s_c = _x_s_c;
    s_timeout = _x_s_timeout;
    r_l = _x_r_l;
    s_msg_id = _x_s_msg_id;
    s_evt = _x_s_evt;
    s_l = _x_s_l;
    delta = _x_delta;
    s2r = _x_s2r;
    r2s = _x_r2s;

  }
}
