extern int __VERIFIER_nondet_int(void);

int nondet_bool(void)
{
  return __VERIFIER_nondet_int() > 0;
}

void f(int w, int x, int y, int z)
{
  if (! (z >= 4)) { return; }
  z = z + 1;

  if (x >= 0) {
    if (! (w <= -5)) { return; }
    z = z + 1;
  } else {
    z = z - 1;
  }

  if (nondet_bool()) {
    if (! (x < 0)) { return; }
    z = z - 1;
    return;
  }

  while (x >= w) {
    if (nondet_bool()) {
      if (! (x < 0)) { return; }
      z = z - 1;
      return;
    }
    if (z <= 8) {
      ;
    } else {
      ;
    }
    x = z*z;
    w = w - 1;
  }
  if (nondet_bool()) {
    if (! (x < 0)) { return; }
    z = z - 1;
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
