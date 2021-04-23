extern int __VERIFIER_nondet_int(void);

void f(int x, int y, int z)
{
  z = 2;
  if (! (x >= y)) { return; }
  x = 5;
  y = 6;

  if (z >= 0) {
    while (x <= y + (-1)) {
      y = z * z;
      x = y;
      y = y + 1;
    }
  } else {
    return;
  }
}

int main() {
  int v1 = __VERIFIER_nondet_int();
  int v2 = __VERIFIER_nondet_int();
  int v3 = __VERIFIER_nondet_int();
  f(v1, v2, v3);
  return 0;
}
