extern float __VERIFIER_nondet_float(void);

int main()
{
  float i = __VERIFIER_nondet_float();
  float j = __VERIFIER_nondet_float();
  while (i >= 0) {
    i = i + j;
    j = j*j*j / 3 + 1;
  }
  return 0;
}
