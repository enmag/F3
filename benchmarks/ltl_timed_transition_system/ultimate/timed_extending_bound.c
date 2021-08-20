//@ ltl invariant negative: ( (<> ([] AP(dec_bound))) || (! ([] (<> AP((1.0 <= _diverge_delta))))));
extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);
typedef enum {false, true} bool;
bool __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}

bool __ok;
float _diverge_delta, _x__diverge_delta;
float delta, _x_delta;
int bound, _x_bound;
float c, _x_c;
bool dec_bound, _x_dec_bound;

int main()
{
  _diverge_delta = __VERIFIER_nondet_float();
  delta = __VERIFIER_nondet_float();
  bound = __VERIFIER_nondet_int();
  c = __VERIFIER_nondet_float();
  dec_bound = __VERIFIER_nondet_bool();

  __ok = (((dec_bound && (0.0 <= delta)) && (c <= ((float)(bound)))) && (delta == _diverge_delta));
  while (__ok) {
    _x__diverge_delta = __VERIFIER_nondet_float();
    _x_delta = __VERIFIER_nondet_float();
    _x_bound = __VERIFIER_nondet_int();
    _x_c = __VERIFIER_nondet_float();
    _x_dec_bound = __VERIFIER_nondet_bool();

    __ok = (((((((0.0 <= _x_delta) && (_x_c <= ((float)(_x_bound)))) && ((delta <= 0.0) || (((c + ((-1.0 * _x_c) + delta)) == 0.0) && (_x_dec_bound && (bound == _x_bound))))) && ((c == _x_c) || ( !(delta == 0.0)))) && ((_x_dec_bound && (bound == _x_bound)) || ( !((delta == 0.0) && ( !(((float)(bound)) <= c)))))) && ((_x_bound <= bound) || ( !_x_dec_bound))) && (((delta == _x__diverge_delta) || ( !(1.0 <= _diverge_delta))) && ((1.0 <= _diverge_delta) || ((delta + (_diverge_delta + (-1.0 * _x__diverge_delta))) == 0.0))));
    _diverge_delta = _x__diverge_delta;
    delta = _x_delta;
    bound = _x_bound;
    c = _x_c;
    dec_bound = _x_dec_bound;

  }
}
