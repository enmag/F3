extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);
typedef enum {false, true} bool;
bool __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}

int main()
{
int x, _x_x;

  int __steps_to_fair = __VERIFIER_nondet_int();
  x = __VERIFIER_nondet_int();

  bool __ok = (0 <= x);
  while (__steps_to_fair >= 0 && __ok) {
    if ((0 <= x)) {
      __steps_to_fair = __VERIFIER_nondet_int();
    } else {
      __steps_to_fair--;
    }
    _x_x = __VERIFIER_nondet_int();

    __ok = (( !(0 < x) || (_x_x < (-1 * (x + 1)))) && ( !(x <= 0) || ((-1 * (x - 1)) < _x_x)));
    x = _x_x;

  }
}
