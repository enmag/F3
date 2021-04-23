//@ ltl invariant negative: ( (! ([] (<> (! AP((r <= i)))))) || (! ([] (<> (! AP((m_x_i <= i)))))));

extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);

char __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}


float m_x_i, _x_m_x_i;
float r, _x_r;
float i, _x_i;

int main()
{
  m_x_i = __VERIFIER_nondet_float();
  r = __VERIFIER_nondet_float();
  i = __VERIFIER_nondet_float();

  int __ok = ((0.0 <= i) && (( !(r <= 0.0)) && ( !(10.0 <= r))));
  while (__ok) {
    _x_m_x_i = __VERIFIER_nondet_float();
    _x_r = __VERIFIER_nondet_float();
    _x_i = __VERIFIER_nondet_float();

    __ok = ((((r == _x_r) && ((10.0 <= i) || (((i + (-1.0 * _x_i)) == -1.0) || (i == _x_i)))) && (( !(10.0 <= i)) || (_x_i == 0.0))) && (m_x_i == _x_i));
    m_x_i = _x_m_x_i;
    r = _x_r;
    i = _x_i;

  }
}
