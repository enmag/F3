extern int __VERIFIER_nondet_int(void);

void f(int n, int d, int log)
{
  if (! (n >= 1)) { return; }
  if (! (d >= 2)) { return; }
  log = 0;

  while (n >= 0) {
    n = n/d;
    log = log + 1;
  }
}

int main()
{
  int v1 = __VERIFIER_nondet_int();
  int v2 = __VERIFIER_nondet_int();
  int v3 = __VERIFIER_nondet_int();
  f(v1, v2, v3);
  return 0;
}
