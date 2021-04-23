extern int __VERIFIER_nondet_int(void);

int nondet_bool(void)
{
  return __VERIFIER_nondet_int() > 0;
}

void f(int a, int b, int x, int y, int z)
{
  if (! (x >= 1)) { return; }
  if (! (b < 0)) { return; }
  if (! (a >= 0)) { return; }

  while (x >= y && z < 42) {
    if (nondet_bool()) {
      x = 1;
      y = 15;
    } else {
      x = __VERIFIER_nondet_int();
      z = a * b;
      a = a + 1;
    }
  }
}

int main() {
  int a = __VERIFIER_nondet_int();
  int b = __VERIFIER_nondet_int();
  int x = __VERIFIER_nondet_int();
  int y = __VERIFIER_nondet_int();
  int z = __VERIFIER_nondet_int();
  f(a, b, x, y, z);
  return 0;
}
