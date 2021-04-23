extern int __VERIFIER_nondet_int(void);

void f(int w, int x, int y, int z)
{
  z = z + 1;

  if (x >= 0) {
    if (! (w <= -5)) { return; }
    z = z + 1;
  } else {
    z = z - 1;
  }

  while (x >= w) {
    x = z * z;
    w = w - 1;
  }
  z = z - 1;
}

int main() {
  int v1 = __VERIFIER_nondet_int();
  int v2 = __VERIFIER_nondet_int();
  int v3 = __VERIFIER_nondet_int();
  int v4 = __VERIFIER_nondet_int();
  f(v1, v2, v3, v4);
  return 0;
}
