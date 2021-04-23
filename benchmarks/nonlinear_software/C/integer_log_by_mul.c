extern int __VERIFIER_nondet_int(void);

void f(int n, int d, int log, int firstMultiply)
{
  if (! (n >= 1)) { return; }
  if (! (d >= 0)) { return; }

  if (d < 2) {
    log = 0;
    firstMultiply = d;
    while (d <= n) {
      log = log + 1;
      d = d * firstMultiply;
    }
  } else {
    ;
  }
}

int main()
{
  int v1 = __VERIFIER_nondet_int();
  int v2 = __VERIFIER_nondet_int();
  int v3 = __VERIFIER_nondet_int();
  int v4 = __VERIFIER_nondet_int();
  f(v1, v2, v3, v4);
  return 0;
}
