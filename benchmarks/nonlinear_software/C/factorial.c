extern int __VERIFIER_nondet_int(void);

void f(int n, int i, int fact)
{
  if (! (n >= 1)) { return; }
  fact = 2;
  i = 1;

  while (i <= fact) {
    fact = fact * i;
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
