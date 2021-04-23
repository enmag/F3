extern int __VERIFIER_nondet_int(void);

void f(int x, int y, int z)
{
  if (! (x <= y + (-1))) { return; }

  while (x <= y + (-1)) {
    y = z * z;
    x = y;
    y = y + 1;
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
