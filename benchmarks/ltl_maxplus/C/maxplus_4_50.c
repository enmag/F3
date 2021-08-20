extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);
typedef enum {false, true} bool;
bool __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}

int main()
{
float x_0, _x_x_0;
float x_1, _x_x_1;
float x_3, _x_x_3;
float x_2, _x_x_2;

  int __steps_to_fair = __VERIFIER_nondet_int();
  x_0 = __VERIFIER_nondet_float();
  x_1 = __VERIFIER_nondet_float();
  x_3 = __VERIFIER_nondet_float();
  x_2 = __VERIFIER_nondet_float();

  bool __ok = (1 && ( !(((x_2 + (-1.0 * x_3)) <= 7.0) || (((x_0 + (-1.0 * x_2)) <= -15.0) && ((x_0 + (-1.0 * x_3)) <= 9.0)))));
  while (__steps_to_fair >= 0 && __ok) {
    if (( !0)) {
      __steps_to_fair = __VERIFIER_nondet_int();
    } else {
      __steps_to_fair--;
    }
    _x_x_0 = __VERIFIER_nondet_float();
    _x_x_1 = __VERIFIER_nondet_float();
    _x_x_3 = __VERIFIER_nondet_float();
    _x_x_2 = __VERIFIER_nondet_float();

    __ok = ((((((((x_2 + (-1.0 * _x_x_0)) <= -17.0) && ((x_3 + (-1.0 * _x_x_0)) <= -2.0)) && (((x_2 + (-1.0 * _x_x_0)) == -17.0) || ((x_3 + (-1.0 * _x_x_0)) == -2.0))) && ((((x_2 + (-1.0 * _x_x_1)) <= -14.0) && ((x_3 + (-1.0 * _x_x_1)) <= -1.0)) && (((x_2 + (-1.0 * _x_x_1)) == -14.0) || ((x_3 + (-1.0 * _x_x_1)) == -1.0)))) && ((((x_0 + (-1.0 * _x_x_2)) <= -19.0) && ((x_2 + (-1.0 * _x_x_2)) <= -4.0)) && (((x_0 + (-1.0 * _x_x_2)) == -19.0) || ((x_2 + (-1.0 * _x_x_2)) == -4.0)))) && ((((x_1 + (-1.0 * _x_x_3)) <= -20.0) && ((x_2 + (-1.0 * _x_x_3)) <= -10.0)) && (((x_1 + (-1.0 * _x_x_3)) == -20.0) || ((x_2 + (-1.0 * _x_x_3)) == -10.0)))) && 1);
    x_0 = _x_x_0;
    x_1 = _x_x_1;
    x_3 = _x_x_3;
    x_2 = _x_x_2;

  }
}
