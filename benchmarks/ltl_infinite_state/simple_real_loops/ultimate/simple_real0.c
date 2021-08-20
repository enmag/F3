//@ ltl invariant negative: <> [] AP((0.0 <= x));
extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);
typedef enum {false, true} bool;
bool __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}

bool __ok;
float x, _x_x;

int main()
{
  x = __VERIFIER_nondet_float();

  __ok = (0.0 <= x);
  while (__ok) {
    _x_x = __VERIFIER_nondet_float();

    __ok = (( !(0.0 < x) || (_x_x < (-1.0 * (x + 1.0)))) && ( !(x <= 0.0) || ((-1.0 * (x - 1.0)) < _x_x)));
    x = _x_x;

  }
}
