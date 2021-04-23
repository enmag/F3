extern int __VERIFIER_nondet_int(void);

void f(int x, int y, int z)
{
  if (! (x >= -1)) { return; }
  if (! (y >= -10)) { return; }

  while (x >= 1 && y >= -10) {
    z = x * y;
    x = y;
    x = y + 1;
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
