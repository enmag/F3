extern int __VERIFIER_nondet_int(void);

void f(int x, int y, int z)
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
    x = z*z - y*z;
  }
}

int main() {
  int v1 = __VERIFIER_nondet_int();
  int v2 = __VERIFIER_nondet_int();
  int v3 = __VERIFIER_nondet_int();
  f(v1, v2, v3);
  return 0;
}
