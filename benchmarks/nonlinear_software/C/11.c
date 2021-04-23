extern int __VERIFIER_nondet_int(void);

void f(int w, int x, int y, int z)
{
  if (! (z >= 5)) { return; }
  if (! (y <= 2)) { return; }
  if (! (w <= -5)) { return; }

  while (x >= y) {
    x = -1 * z * w;
    z = z + 1;
    w = w - 1;
  }

}

int main() {
  int v1 = __VERIFIER_nondet_int();
  int v2 = __VERIFIER_nondet_int();
  int v3 = __VERIFIER_nondet_int();
  int v4 = __VERIFIER_nondet_int();
  f(v1, v2, v3, v4);
  return 0;
}
