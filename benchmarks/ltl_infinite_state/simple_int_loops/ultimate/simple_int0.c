//@ ltl invariant negative: <> [] AP((0 <= x));

extern int __VERIFIER_nondet_int(void);

char __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}


int x, _x_x;

int main()
{
  x = __VERIFIER_nondet_int();

  int __ok = (0 <= x);
  while (__ok) {
    _x_x = __VERIFIER_nondet_int();

    __ok = (( !(0 < x) || (_x_x < (-1 * (x + 1)))) && ( !(x <= 0) || ((-1 * (x - 1)) < _x_x)));
    x = _x_x;

  }
}
