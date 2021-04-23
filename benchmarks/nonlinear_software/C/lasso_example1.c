extern int __VERIFIER_nondet_int(void);

void f(int i, int j, int k)
{
  if (! (j >= 2)) { return; }
  if (! (k >= 3)) { return; }

  while (i >= 0) {
    i = j * k;
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
