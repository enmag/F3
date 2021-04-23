extern int __VERIFIER_nondet_int(void);

void f(int a, int b, int x, int y, int z)
{
  if (! (z >= 4)) { return; }
  z = z + 1;

  if (x >= 0) {
    z = z + 1;
  } else {
    z = z - 1;
  }

  if (! (y >= 2)) { return; }
  if (! (y <= 5)) { return; }

  while (x >= 0) {
    a = z*z;
    b = y*z;
    x = a - b;
  }
}

int main()
{
  int v1 = __VERIFIER_nondet_int();
  int v2 = __VERIFIER_nondet_int();
  int v3 = __VERIFIER_nondet_int();
  int v4 = __VERIFIER_nondet_int();
  int v5 = __VERIFIER_nondet_int();
  f(v1, v2, v3, v4, v5);
  return 0;
}
