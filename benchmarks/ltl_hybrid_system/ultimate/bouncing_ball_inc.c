//@ ltl invariant negative: ( (<> ([] (! AP((h == 0.0))))) || (! ([] (<> AP((1.0 <= _diverge_delta))))));
extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);
typedef enum {false, true} bool;
bool __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}

bool __ok;
float _diverge_delta, _x__diverge_delta;
float v, _x_v;
float delta, _x_delta;
float h, _x_h;

int main()
{
  _diverge_delta = __VERIFIER_nondet_float();
  v = __VERIFIER_nondet_float();
  delta = __VERIFIER_nondet_float();
  h = __VERIFIER_nondet_float();

  __ok = ((((((h == 0.0) && (v == (981.0/100.0))) && ((delta == 0.0) || ( !((h == 0.0) && ( !(0.0 <= v)))))) && (0.0 <= delta)) && (0.0 <= h)) && (delta == _diverge_delta));
  while (__ok) {
    _x__diverge_delta = __VERIFIER_nondet_float();
    _x_v = __VERIFIER_nondet_float();
    _x_delta = __VERIFIER_nondet_float();
    _x_h = __VERIFIER_nondet_float();

    __ok = (((((((_x_delta == 0.0) || ( !((_x_h == 0.0) && ( !(0.0 <= _x_v))))) && (0.0 <= _x_delta)) && (0.0 <= _x_h)) && ((( !((h == 0.0) && ( !(0.0 <= v)))) || (_x_h == 0.0)) && (((h == 0.0) && ( !(0.0 <= v))) || (((200.0 * h) + ((-200.0 * _x_h) + ((-981.0 * (delta * delta)) + (200.0 * (v * delta))))) == 0.0)))) && ((( !((h == 0.0) && ( !(0.0 <= v)))) || (((11.0 * v) + (10.0 * _x_v)) == 0.0)) && (((h == 0.0) && ( !(0.0 <= v))) || (((100.0 * v) + ((-100.0 * _x_v) + (-981.0 * delta))) == 0.0)))) && (((delta == _x__diverge_delta) || ( !(1.0 <= _diverge_delta))) && ((1.0 <= _diverge_delta) || ((delta + (_diverge_delta + (-1.0 * _x__diverge_delta))) == 0.0))));
    _diverge_delta = _x__diverge_delta;
    v = _x_v;
    delta = _x_delta;
    h = _x_h;

  }
}
