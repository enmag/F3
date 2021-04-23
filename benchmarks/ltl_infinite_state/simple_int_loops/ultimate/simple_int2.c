//@ ltl invariant negative: <> [] AP((0 < x));

extern int __VERIFIER_nondet_int(void);

char __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}


char b, _x_b;
int x, _x_x;

int main()
{
  b = __VERIFIER_nondet_bool();
  x = __VERIFIER_nondet_int();

  int __ok = (0 <= x);
  while (__ok) {
    _x_b = __VERIFIER_nondet_bool();
    _x_x = __VERIFIER_nondet_int();

    __ok = (( !(b != 0) || ((_x_x < (-1 * (x + 1))) && ( !(_x_b != 0)))) && ( !( !(b != 0)) || (((-1 * (x - 1)) < _x_x) && (_x_b != 0))));
    b = _x_b;
    x = _x_x;

  }
}
