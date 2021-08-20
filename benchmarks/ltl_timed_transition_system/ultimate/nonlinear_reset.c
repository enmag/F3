//@ ltl invariant negative: ( (<> ([] ( (! AP((delta <= 0.0))) || (! AP((c == bound)))))) || (! ([] (<> AP((1.0 <= _diverge_delta))))));
extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);
typedef enum {false, true} bool;
bool __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}

bool __ok;
float _diverge_delta, _x__diverge_delta;
float delta, _x_delta;
int counter, _x_counter;
float c, _x_c;
float bound, _x_bound;

int main()
{
  _diverge_delta = __VERIFIER_nondet_float();
  delta = __VERIFIER_nondet_float();
  counter = __VERIFIER_nondet_int();
  c = __VERIFIER_nondet_float();
  bound = __VERIFIER_nondet_float();

  __ok = (((0.0 <= delta) && ((c == 0.0) && (counter == 0))) && (delta == _diverge_delta));
  while (__ok) {
    _x__diverge_delta = __VERIFIER_nondet_float();
    _x_delta = __VERIFIER_nondet_float();
    _x_counter = __VERIFIER_nondet_int();
    _x_c = __VERIFIER_nondet_float();
    _x_bound = __VERIFIER_nondet_float();

    __ok = (((((0.0 <= _x_delta) && ((delta <= 0.0) || (((c + ((-1.0 * _x_c) + delta)) == 0.0) && (counter == _x_counter)))) && ((((counter + (-1 * _x_counter)) == -1) && (_x_c == ((float)((counter * counter))))) || ( !((delta == 0.0) && (c == bound))))) && (((counter == _x_counter) && (c == _x_c)) || ( !((delta == 0.0) && ( !(c == bound)))))) && (((delta == _x__diverge_delta) || ( !(1.0 <= _diverge_delta))) && ((1.0 <= _diverge_delta) || ((delta + (_diverge_delta + (-1.0 * _x__diverge_delta))) == 0.0))));
    _diverge_delta = _x__diverge_delta;
    delta = _x_delta;
    counter = _x_counter;
    c = _x_c;
    bound = _x_bound;

  }
}
