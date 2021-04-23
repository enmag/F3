//@ ltl invariant negative: ( (<> ([] AP((dec_bound != 0)))) || (! ([] (<> AP((1.0 <= _diverge_delta))))));

extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);

char __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}


float _diverge_delta, _x__diverge_delta;
char dec_bound, _x_dec_bound;
float delta, _x_delta;
int bound, _x_bound;
float c, _x_c;

int main()
{
  _diverge_delta = __VERIFIER_nondet_float();
  dec_bound = __VERIFIER_nondet_bool();
  delta = __VERIFIER_nondet_float();
  bound = __VERIFIER_nondet_int();
  c = __VERIFIER_nondet_float();

  int __ok = ((((dec_bound != 0) && (0.0 <= delta)) && (c <= (float)bound)) && (delta == _diverge_delta));
  while (__ok) {
    _x__diverge_delta = __VERIFIER_nondet_float();
    _x_dec_bound = __VERIFIER_nondet_bool();
    _x_delta = __VERIFIER_nondet_float();
    _x_bound = __VERIFIER_nondet_int();
    _x_c = __VERIFIER_nondet_float();

    __ok = (((((((0.0 <= _x_delta) && (_x_c <= (float)_x_bound)) && ((delta <= 0.0) || (((c + ((-1.0 * _x_c) + delta)) == 0.0) && ((_x_dec_bound != 0) && (bound == _x_bound))))) && ((c == _x_c) || ( !(delta == 0.0)))) && (((_x_dec_bound != 0) && (bound == _x_bound)) || ( !((delta == 0.0) && ( !((float)bound <= c)))))) && ((_x_bound <= bound) || ( !(_x_dec_bound != 0)))) && (((delta == _x__diverge_delta) || ( !(1.0 <= _diverge_delta))) && ((1.0 <= _diverge_delta) || ((delta + (_diverge_delta + (-1.0 * _x__diverge_delta))) == 0.0))));
    _diverge_delta = _x__diverge_delta;
    dec_bound = _x_dec_bound;
    delta = _x_delta;
    bound = _x_bound;
    c = _x_c;

  }
}
