//@ ltl invariant negative: ( (<> ([] (! AP((h == 0.0))))) || (! ([] (<> AP((1.0 <= _diverge_delta))))));

extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);

char __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}


float _diverge_delta, _x__diverge_delta;
float v, _x_v;
float h, _x_h;
float delta, _x_delta;

int main()
{
  _diverge_delta = __VERIFIER_nondet_float();
  v = __VERIFIER_nondet_float();
  h = __VERIFIER_nondet_float();
  delta = __VERIFIER_nondet_float();

  int __ok = (((h == 0.0) && (v == 9.81)) && (delta == _diverge_delta));
  while (__ok) {
    _x__diverge_delta = __VERIFIER_nondet_float();
    _x_v = __VERIFIER_nondet_float();
    _x_h = __VERIFIER_nondet_float();
    _x_delta = __VERIFIER_nondet_float();

    __ok = (((((_x_h == 0.0) && ((v + (2.0 * _x_v)) == 0.0)) || ( !((h == 0.0) && ( !(0.0 <= v))))) && (((h == 0.0) && ( !(0.0 <= v))) || ((((200.0 * h) + ((-200.0 * _x_h) + ((200.0 * (delta * v)) + (-981.0 * (delta * delta))))) == 0.0) && (((981.0 * delta) + ((-100.0 * v) + (100.0 * _x_v))) == 0.0)))) && (((delta == _x__diverge_delta) || ( !(1.0 <= _diverge_delta))) && ((1.0 <= _diverge_delta) || ((delta + (_diverge_delta + (-1.0 * _x__diverge_delta))) == 0.0))));
    _diverge_delta = _x__diverge_delta;
    v = _x_v;
    h = _x_h;
    delta = _x_delta;

  }
}
