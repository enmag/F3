extern int __VERIFIER_nondet_int(void);

int nondet_bool(void)
{
  return __VERIFIER_nondet_int() > 0;
}

void f(int x, int y)
{
  if (! (x >= 1)) { return; }

  while (x >= 0) {
    if (! (y >= 32)) { return; }
    if (nondet_bool()) {
      x = 1;
      y = 15;
    } else {
      x = __VERIFIER_nondet_int();
      y = x;
    }
  }
}

int main() {
  int v1 = __VERIFIER_nondet_int();
  int v2 = __VERIFIER_nondet_int();
  f(v1, v2);
  return 0;
}
