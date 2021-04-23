extern int __VERIFIER_nondet_int(void);

void f(int x, int y, int z)
{
  if (! (z >= 2)) { return; }
  if (! (y >= 3)) { return; }

  while (z >= -5) {
    while (x >= 0) {
      x = z/y;
      y = y + 1;
      z = z + 1;
    }
  }
}

int main() {
  int v1 = __VERIFIER_nondet_int();
  int v2 = __VERIFIER_nondet_int();
  int v3 = __VERIFIER_nondet_int();
  f(v1, v2, v3);
  return 0;
}
