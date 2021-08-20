extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);
typedef enum {false, true} bool;
bool __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}

int main()
{
bool b, _x_b;
int x, _x_x;

  int __steps_to_fair = __VERIFIER_nondet_int();
  b = __VERIFIER_nondet_bool();
  x = __VERIFIER_nondet_int();

  bool __ok = (0 <= x);
  while (__steps_to_fair >= 0 && __ok) {
    if ((0 < x)) {
      __steps_to_fair = __VERIFIER_nondet_int();
    } else {
      __steps_to_fair--;
    }
    _x_b = __VERIFIER_nondet_bool();
    _x_x = __VERIFIER_nondet_int();

    __ok = (( !b || ((_x_x < (-1 * (x + 1))) && ( !_x_b))) && ( !( !b) || (((-1 * (x - 1)) < _x_x) && _x_b)));
    b = _x_b;
    x = _x_x;

  }
}
