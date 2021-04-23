extern int __VERIFIER_nondet_int(void);

int nondet_bool(void)
{
  return __VERIFIER_nondet_int() > 0;
}

void f(int w, int x, int y, int z)
{
  if (! (z >= 3)) { return; }
  if (! (y >= 2)) { return; }

  if (nondet_bool()) {
    if (! (z < -5)) { return; }
    return;
  }
  while (w >= 2) {
    if (nondet_bool()) {
      if (! (z < -5)) { return; }
      return;
    }
    while (x >= 0) {
      x = z * y + (w/y);
      y = y + 1;
      z = z + 1;
    }
  }
  if (nondet_bool()) {
    if (! (z < -5)) { return; }
    return;
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
