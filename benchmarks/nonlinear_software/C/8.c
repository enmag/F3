extern int __VERIFIER_nondet_int(void);

void f(int z)
{
  if (! (z >= 3)) { return; }

  while (z >= 3) {
    z = __VERIFIER_nondet_int();
  }
}

int main() {
  int v1 = __VERIFIER_nondet_int();
  f(v1);
  return 0;
}
