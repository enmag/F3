extern int __VERIFIER_nondet_int(void);

int nondet_bool(void)
{
  return __VERIFIER_nondet_int() > 0;
}

void f(int n_number, int numerator, int denominator,
       int nmul, int dmul, int r_number, int nCr)
{
  if (! (n_number >= 1)) { return; }
  numerator = 1;
  denominator = 1;
  nmul = n_number;
  dmul = r_number;
  nCr = 1;
  if (n_number >= r_number) {
    if (nondet_bool()) { // 2 -> 5 -> 6
      if (! (numerator < 1)) { return; }
      nCr = numerator / denominator;
      return;
    }

    while (nCr >= 1) {
      if (nondet_bool()) { // 2 -> 5 -> 6
        if (! (numerator < 1)) { return; }
        nCr = numerator / denominator;
        return;
      }
      numerator = numerator * nmul;
      nmul = nmul - 1;
      denominator = denominator * dmul;
      dmul = dmul - 1;
    }
    if (nondet_bool()) { // 2 -> 5 -> 6
      if (! (numerator < 1)) { return; }
      nCr = numerator / denominator;
      return;
    }
  } else {
    ;
  }
}

int main()
{
  int v1 = __VERIFIER_nondet_int();
  int v2 = __VERIFIER_nondet_int();
  int v3 = __VERIFIER_nondet_int();
  int v4 = __VERIFIER_nondet_int();
  int v5 = __VERIFIER_nondet_int();
  int v6 = __VERIFIER_nondet_int();
  int v7 = __VERIFIER_nondet_int();
  f(v1, v2, v3, v4, v5, v6, v7);
  return 0;
}
