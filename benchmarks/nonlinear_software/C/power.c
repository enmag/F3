extern int __VERIFIER_nondet_int(void);

void f(int n, int i, int exp)
{
  if (! (n >= 2)) { return; }
  i = 1;
  exp = 1;
  while (i <= exp) {
    exp = exp * n;
    i = i + 1;
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
