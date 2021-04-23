//@ ltl invariant negative: ( (! ([] (<> (! AP((r <= i)))))) || (! ([] (<> AP((inc_i != 0))))));

extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);

char __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}


char inc_i, _x_inc_i;
float l, _x_l;
float r, _x_r;
float i, _x_i;

int main()
{
  inc_i = __VERIFIER_nondet_bool();
  l = __VERIFIER_nondet_float();
  r = __VERIFIER_nondet_float();
  i = __VERIFIER_nondet_float();

  int __ok = (((( !(r <= 0.0)) && ( !(l <= r))) && ((0.0 <= i) && ( !(inc_i != 0)))) && ( !(l <= 0.0)));
  while (__ok) {
    _x_inc_i = __VERIFIER_nondet_bool();
    _x_l = __VERIFIER_nondet_float();
    _x_r = __VERIFIER_nondet_float();
    _x_i = __VERIFIER_nondet_float();

    __ok = (((r == _x_r) && ((l <= i) || (((i + (-1.0 * _x_i)) == -1.0) && ((_x_inc_i != 0) && (l == _x_l))))) && (( !(l <= i)) || ((_x_i == 0.0) && (((l + (-1.0 * _x_l)) == -1.0) && ( !(_x_inc_i != 0))))));
    inc_i = _x_inc_i;
    l = _x_l;
    r = _x_r;
    i = _x_i;

  }
}
