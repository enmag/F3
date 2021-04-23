//@ ltl invariant negative: <> [] AP((0.0 < x));

extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);

char __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}


char b, _x_b;
float x, _x_x;

int main()
{
  b = __VERIFIER_nondet_bool();
  x = __VERIFIER_nondet_float();

  int __ok = (0.0 <= x);
  while (__ok) {
    _x_b = __VERIFIER_nondet_bool();
    _x_x = __VERIFIER_nondet_float();

    __ok = (( !(b != 0) || (_x_x < (-1.0 * (x + 1.0)))) && ( !( !(b != 0)) || ((-1.0 * (x - 1.0)) < _x_x)));
    b = _x_b;
    x = _x_x;

  }
}
