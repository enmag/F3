//@ ltl invariant negative: ( (<> ([] (! ( AP((h == 0.0)) && (! AP((v <= 0.0))))))) || (! ([] (<> AP((1.0 <= _diverge_delta))))));

extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);

char __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}

char stop, _x_stop;
float _diverge_delta, _x__diverge_delta;
float counter, _x_counter;
float delta, _x_delta;
float v, _x_v;
float h, _x_h;

int main()
{
  stop = __VERIFIER_nondet_bool();
  _diverge_delta = __VERIFIER_nondet_float();
  counter = __VERIFIER_nondet_float();
  delta = __VERIFIER_nondet_float();
  v = __VERIFIER_nondet_float();
  h = __VERIFIER_nondet_float();

  int __ok = ((((counter == 1.0) && (h == 0.0)) && (v == 9.81)) && (delta == _diverge_delta));
  while (__ok) {
    _x_stop = __VERIFIER_nondet_bool();
    _x__diverge_delta = __VERIFIER_nondet_float();
    _x_counter = __VERIFIER_nondet_float();
    _x_delta = __VERIFIER_nondet_float();
    _x_v = __VERIFIER_nondet_float();
    _x_h = __VERIFIER_nondet_float();

    __ok = (((((((counter + (-1.0 * _x_counter)) == -1.0) || ( !((h == 0.0) && ( !(0.0 <= v))))) && (((h == 0.0) && ( !(0.0 <= v))) || (counter == _x_counter))) && (((_x_h == 0.0) || ( !((h == 0.0) && ((stop != 0) || (v <= 0.0))))) && (((h == 0.0) && ((stop != 0) || (v <= 0.0))) || (((200.0 * h) + ((-200.0 * _x_h) + ((200.0 * (v * delta)) + (-981.0 * (delta * delta))))) == 0.0)))) && (((_x_v == 0.0) || ( !((stop != 0) && (h == 0.0)))) && ((((_x_v + ((v * counter) / (counter + 1.0))) == 0.0) || ( !(( !(stop != 0)) && ((h == 0.0) && (v <= 0.0))))) && ((((stop != 0) && (h == 0.0)) && (( !(stop != 0)) && ((h == 0.0) && (v <= 0.0)))) || (((100.0 * v) + ((-100.0 * _x_v) + (-981.0 * delta))) == 0.0))))) && (((delta == _x__diverge_delta) || ( !(1.0 <= _diverge_delta))) && ((1.0 <= _diverge_delta) || ((delta + (_diverge_delta + (-1.0 * _x__diverge_delta))) == 0.0))));
    stop = _x_stop;
    _diverge_delta = _x__diverge_delta;
    counter = _x_counter;
    delta = _x_delta;
    v = _x_v;
    h = _x_h;

  }
}
