extern int __VERIFIER_nondet_int(void);

int nondet_bool(void)
{
  return __VERIFIER_nondet_int() > 0;
}

void f(int x, int y, int z)
{
  if (! (x >= -1)) { return; }
  if (! (y <= -10)) { return; }

  while (x >= 1 && y <= -20) {
    if (nondet_bool()) {
      if (! (x < 0)) { return; }
    }
    z = x * y;
    x = x - 2*y;
    y = y - 1;
  }
}

int main() {
  int v1 = __VERIFIER_nondet_int();
  int v2 = __VERIFIER_nondet_int();
  int v3 = __VERIFIER_nondet_int();
  f(v1, v2, v3);
  return 0;
}
