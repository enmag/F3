//@ ltl invariant negative: ( (! ([] (<> (! AP((r <= i)))))) || (! ([] (<> AP(inc_i)))));
extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);
typedef enum {false, true} bool;
bool __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}

bool __ok;
bool inc_i, _x_inc_i;
float i, _x_i;
float l, _x_l;
float r, _x_r;

int main()
{
  inc_i = __VERIFIER_nondet_bool();
  i = __VERIFIER_nondet_float();
  l = __VERIFIER_nondet_float();
  r = __VERIFIER_nondet_float();

  __ok = (((( !(r <= 0.0)) && ( !(l <= r))) && ((0.0 <= i) && ( !inc_i))) && ( !(l <= 0.0)));
  while (__ok) {
    _x_inc_i = __VERIFIER_nondet_bool();
    _x_i = __VERIFIER_nondet_float();
    _x_l = __VERIFIER_nondet_float();
    _x_r = __VERIFIER_nondet_float();

    __ok = (((r == _x_r) && ((l <= i) || (((_x_inc_i && ((i + (-1.0 * _x_i)) == -1.0)) || (( !_x_inc_i) && (i == _x_i))) && (l == _x_l)))) && (( !(l <= i)) || (( !_x_inc_i) && ((_x_i == 0.0) && ((l + (-1.0 * _x_l)) == -1.0)))));
    inc_i = _x_inc_i;
    i = _x_i;
    l = _x_l;
    r = _x_r;

  }
}
