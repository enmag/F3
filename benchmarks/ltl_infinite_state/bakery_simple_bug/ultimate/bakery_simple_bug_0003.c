//@ ltl invariant negative: ( ([] (<> AP((num0 == 0)))) || (! ([] ( (<> ( (! AP((p0_l0 != 0))) && (! AP((p0_l1 != 0))))) && (<> (! ( (! AP((p0_l0 != 0))) && (! AP((p0_l1 != 0))))))))));

extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);

char __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}


char p0_l0, _x_p0_l0;
char p2_l0, _x_p2_l0;
int num2, _x_num2;
int num1, _x_num1;
char p0_l1, _x_p0_l1;
int num0, _x_num0;
char run1, _x_run1;
char p1_l1, _x_p1_l1;
char run0, _x_run0;
char p1_l0, _x_p1_l0;
int max_num, _x_max_num;
char p2_l1, _x_p2_l1;
int min_num, _x_min_num;

int main()
{
  p0_l0 = __VERIFIER_nondet_bool();
  p2_l0 = __VERIFIER_nondet_bool();
  num2 = __VERIFIER_nondet_int();
  num1 = __VERIFIER_nondet_int();
  p0_l1 = __VERIFIER_nondet_bool();
  num0 = __VERIFIER_nondet_int();
  run1 = __VERIFIER_nondet_bool();
  p1_l1 = __VERIFIER_nondet_bool();
  run0 = __VERIFIER_nondet_bool();
  p1_l0 = __VERIFIER_nondet_bool();
  max_num = __VERIFIER_nondet_int();
  p2_l1 = __VERIFIER_nondet_bool();
  min_num = __VERIFIER_nondet_int();

  int __ok = (((( !(p2_l0 != 0)) && ( !(p2_l1 != 0))) && (((( !(p2_l0 != 0)) && ( !(p2_l1 != 0))) || ((p2_l0 != 0) && ( !(p2_l1 != 0)))) || (((p2_l1 != 0) && ( !(p2_l0 != 0))) || ((p2_l0 != 0) && (p2_l1 != 0))))) && (((( !(p1_l0 != 0)) && ( !(p1_l1 != 0))) && (((( !(p1_l0 != 0)) && ( !(p1_l1 != 0))) || ((p1_l0 != 0) && ( !(p1_l1 != 0)))) || (((p1_l1 != 0) && ( !(p1_l0 != 0))) || ((p1_l0 != 0) && (p1_l1 != 0))))) && (((( !(p0_l0 != 0)) && ( !(p0_l1 != 0))) && (((( !(p0_l0 != 0)) && ( !(p0_l1 != 0))) || ((p0_l0 != 0) && ( !(p0_l1 != 0)))) || (((p0_l1 != 0) && ( !(p0_l0 != 0))) || ((p0_l0 != 0) && (p0_l1 != 0))))) && (((((((((((((num0 == 0) && (num1 == 0)) && (num2 == 0)) && (((run1 != 0) && ( !(run0 != 0))) || ((( !(run0 != 0)) && ( !(run1 != 0))) || ((run0 != 0) && ( !(run1 != 0)))))) && (num0 <= max_num)) && (num1 <= max_num)) && (num2 <= max_num)) && (((num0 == max_num) || (num1 == max_num)) || (num2 == max_num))) && ((((num0 == 0) && (num1 == 0)) && (num2 == 0)) == (min_num == 0))) && ((num0 <= 0) || (min_num <= num0))) && ((num1 <= 0) || (min_num <= num1))) && ((num2 <= 0) || (min_num <= num2))) && (((num0 == min_num) || (num1 == min_num)) || (num2 == min_num))))));
  while (__ok) {
    _x_p0_l0 = __VERIFIER_nondet_bool();
    _x_p2_l0 = __VERIFIER_nondet_bool();
    _x_num2 = __VERIFIER_nondet_int();
    _x_num1 = __VERIFIER_nondet_int();
    _x_p0_l1 = __VERIFIER_nondet_bool();
    _x_num0 = __VERIFIER_nondet_int();
    _x_run1 = __VERIFIER_nondet_bool();
    _x_p1_l1 = __VERIFIER_nondet_bool();
    _x_run0 = __VERIFIER_nondet_bool();
    _x_p1_l0 = __VERIFIER_nondet_bool();
    _x_max_num = __VERIFIER_nondet_int();
    _x_p2_l1 = __VERIFIER_nondet_bool();
    _x_min_num = __VERIFIER_nondet_int();

    __ok = ((((((((((( !(_x_p2_l0 != 0)) && ( !(_x_p2_l1 != 0))) || ((_x_p2_l0 != 0) && ( !(_x_p2_l1 != 0)))) || (((_x_p2_l1 != 0) && ( !(_x_p2_l0 != 0))) || ((_x_p2_l0 != 0) && (_x_p2_l1 != 0)))) && (((run1 != 0) && ( !(run0 != 0))) || ((((p2_l0 != 0) == (_x_p2_l0 != 0)) && ((p2_l1 != 0) == (_x_p2_l1 != 0))) && (num2 == _x_num2)))) && ((((_x_p2_l0 != 0) && ( !(_x_p2_l1 != 0))) && ((_x_num2 + (-1 * max_num)) == 1)) || ( !(((run1 != 0) && ( !(run0 != 0))) && (( !(p2_l0 != 0)) && ( !(p2_l1 != 0))))))) && (((num2 == _x_num2) && (((_x_p2_l0 != 0) && ( !(_x_p2_l1 != 0))) || ((_x_p2_l1 != 0) && ( !(_x_p2_l0 != 0))))) || ( !(((run1 != 0) && ( !(run0 != 0))) && ((p2_l0 != 0) && ( !(p2_l1 != 0))))))) && (( !(((run1 != 0) && ( !(run0 != 0))) && ((p2_l0 != 0) && ( !(p2_l1 != 0))))) || (((_x_p2_l1 != 0) && ( !(_x_p2_l0 != 0))) == ((( !(num0 == min_num)) && (num2 <= min_num)) && ( !(num1 == min_num)))))) && (((num2 == _x_num2) && (((_x_p2_l1 != 0) && ( !(_x_p2_l0 != 0))) || ((_x_p2_l0 != 0) && (_x_p2_l1 != 0)))) || ( !(((run1 != 0) && ( !(run0 != 0))) && ((p2_l1 != 0) && ( !(p2_l0 != 0))))))) && (((( !(_x_p2_l0 != 0)) && ( !(_x_p2_l1 != 0))) && (num2 == _x_num2)) || ( !(((run1 != 0) && ( !(run0 != 0))) && ((p2_l0 != 0) && (p2_l1 != 0)))))) && ((((((((((( !(_x_p1_l0 != 0)) && ( !(_x_p1_l1 != 0))) || ((_x_p1_l0 != 0) && ( !(_x_p1_l1 != 0)))) || (((_x_p1_l1 != 0) && ( !(_x_p1_l0 != 0))) || ((_x_p1_l0 != 0) && (_x_p1_l1 != 0)))) && (((run0 != 0) && ( !(run1 != 0))) || ((((p1_l0 != 0) == (_x_p1_l0 != 0)) && ((p1_l1 != 0) == (_x_p1_l1 != 0))) && (num1 == _x_num1)))) && ((((_x_p1_l0 != 0) && ( !(_x_p1_l1 != 0))) && ((_x_num1 + (-1 * max_num)) == 1)) || ( !(((run0 != 0) && ( !(run1 != 0))) && (( !(p1_l0 != 0)) && ( !(p1_l1 != 0))))))) && (((num1 == _x_num1) && (((_x_p1_l0 != 0) && ( !(_x_p1_l1 != 0))) || ((_x_p1_l1 != 0) && ( !(_x_p1_l0 != 0))))) || ( !(((run0 != 0) && ( !(run1 != 0))) && ((p1_l0 != 0) && ( !(p1_l1 != 0))))))) && (( !(((run0 != 0) && ( !(run1 != 0))) && ((p1_l0 != 0) && ( !(p1_l1 != 0))))) || (((_x_p1_l1 != 0) && ( !(_x_p1_l0 != 0))) == ((num1 <= min_num) && ( !(num0 == min_num)))))) && (((num1 == _x_num1) && (((_x_p1_l1 != 0) && ( !(_x_p1_l0 != 0))) || ((_x_p1_l0 != 0) && (_x_p1_l1 != 0)))) || ( !(((run0 != 0) && ( !(run1 != 0))) && ((p1_l1 != 0) && ( !(p1_l0 != 0))))))) && (((( !(_x_p1_l0 != 0)) && ( !(_x_p1_l1 != 0))) && (num1 == _x_num1)) || ( !(((run0 != 0) && ( !(run1 != 0))) && ((p1_l0 != 0) && (p1_l1 != 0)))))) && ((((((((((( !(_x_p0_l0 != 0)) && ( !(_x_p0_l1 != 0))) || ((_x_p0_l0 != 0) && ( !(_x_p0_l1 != 0)))) || (((_x_p0_l1 != 0) && ( !(_x_p0_l0 != 0))) || ((_x_p0_l0 != 0) && (_x_p0_l1 != 0)))) && ((( !(run0 != 0)) && ( !(run1 != 0))) || ((((p0_l0 != 0) == (_x_p0_l0 != 0)) && ((p0_l1 != 0) == (_x_p0_l1 != 0))) && (num0 == _x_num0)))) && ((((_x_p0_l0 != 0) && ( !(_x_p0_l1 != 0))) && ((_x_num0 + (-1 * max_num)) == 1)) || ( !((( !(run0 != 0)) && ( !(run1 != 0))) && (( !(p0_l0 != 0)) && ( !(p0_l1 != 0))))))) && (((num0 == _x_num0) && (((_x_p0_l0 != 0) && ( !(_x_p0_l1 != 0))) || ((_x_p0_l1 != 0) && ( !(_x_p0_l0 != 0))))) || ( !((( !(run0 != 0)) && ( !(run1 != 0))) && ((p0_l0 != 0) && ( !(p0_l1 != 0))))))) && (( !((( !(run0 != 0)) && ( !(run1 != 0))) && ((p0_l0 != 0) && ( !(p0_l1 != 0))))) || (((_x_p0_l1 != 0) && ( !(_x_p0_l0 != 0))) == (num0 <= min_num)))) && (((num0 == _x_num0) && (((_x_p0_l1 != 0) && ( !(_x_p0_l0 != 0))) || ((_x_p0_l0 != 0) && (_x_p0_l1 != 0)))) || ( !((( !(run0 != 0)) && ( !(run1 != 0))) && ((p0_l1 != 0) && ( !(p0_l0 != 0))))))) && (((( !(_x_p0_l0 != 0)) && ( !(_x_p0_l1 != 0))) && (num0 == _x_num0)) || ( !((( !(run0 != 0)) && ( !(run1 != 0))) && ((p0_l0 != 0) && (p0_l1 != 0)))))) && ((((((((((((_x_run1 != 0) && ( !(_x_run0 != 0))) || ((( !(_x_run0 != 0)) && ( !(_x_run1 != 0))) || ((_x_run0 != 0) && ( !(_x_run1 != 0))))) && (_x_num0 <= _x_max_num)) && (_x_num1 <= _x_max_num)) && (_x_num2 <= _x_max_num)) && (((_x_num0 == _x_max_num) || (_x_num1 == _x_max_num)) || (_x_num2 == _x_max_num))) && ((((_x_num0 == 0) && (_x_num1 == 0)) && (_x_num2 == 0)) == (_x_min_num == 0))) && ((_x_num0 <= 0) || (_x_min_num <= _x_num0))) && ((_x_num1 <= 0) || (_x_min_num <= _x_num1))) && ((_x_num2 <= 0) || (_x_min_num <= _x_num2))) && (((_x_num0 == _x_min_num) || (_x_num1 == _x_min_num)) || (_x_num2 == _x_min_num))))));
    p0_l0 = _x_p0_l0;
    p2_l0 = _x_p2_l0;
    num2 = _x_num2;
    num1 = _x_num1;
    p0_l1 = _x_p0_l1;
    num0 = _x_num0;
    run1 = _x_run1;
    p1_l1 = _x_p1_l1;
    run0 = _x_run0;
    p1_l0 = _x_p1_l0;
    max_num = _x_max_num;
    p2_l1 = _x_p2_l1;
    min_num = _x_min_num;

  }
}
