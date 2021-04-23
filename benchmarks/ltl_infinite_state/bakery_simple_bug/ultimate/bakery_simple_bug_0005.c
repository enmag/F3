//@ ltl invariant negative: ( ([] (<> AP((num0 == 0)))) || (! ([] ( (<> ( (! AP((p0_l0 != 0))) && (! AP((p0_l1 != 0))))) && (<> (! ( (! AP((p0_l0 != 0))) && (! AP((p0_l1 != 0))))))))));

extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);

char __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}


char p3_l1, _x_p3_l1;
char p3_l0, _x_p3_l0;
char p2_l1, _x_p2_l1;
char p2_l0, _x_p2_l0;
char p1_l1, _x_p1_l1;
int min_num, _x_min_num;
int max_num, _x_max_num;
char run0, _x_run0;
char run1, _x_run1;
char run2, _x_run2;
char p0_l0, _x_p0_l0;
int num0, _x_num0;
char p4_l0, _x_p4_l0;
int num1, _x_num1;
char p1_l0, _x_p1_l0;
char p4_l1, _x_p4_l1;
int num2, _x_num2;
int num3, _x_num3;
int num4, _x_num4;
char p0_l1, _x_p0_l1;

int main()
{
  p3_l1 = __VERIFIER_nondet_bool();
  p3_l0 = __VERIFIER_nondet_bool();
  p2_l1 = __VERIFIER_nondet_bool();
  p2_l0 = __VERIFIER_nondet_bool();
  p1_l1 = __VERIFIER_nondet_bool();
  min_num = __VERIFIER_nondet_int();
  max_num = __VERIFIER_nondet_int();
  run0 = __VERIFIER_nondet_bool();
  run1 = __VERIFIER_nondet_bool();
  run2 = __VERIFIER_nondet_bool();
  p0_l0 = __VERIFIER_nondet_bool();
  num0 = __VERIFIER_nondet_int();
  p4_l0 = __VERIFIER_nondet_bool();
  num1 = __VERIFIER_nondet_int();
  p1_l0 = __VERIFIER_nondet_bool();
  p4_l1 = __VERIFIER_nondet_bool();
  num2 = __VERIFIER_nondet_int();
  num3 = __VERIFIER_nondet_int();
  num4 = __VERIFIER_nondet_int();
  p0_l1 = __VERIFIER_nondet_bool();

  int __ok = (((( !(p4_l0 != 0)) && ( !(p4_l1 != 0))) && (((( !(p4_l0 != 0)) && ( !(p4_l1 != 0))) || ((p4_l0 != 0) && ( !(p4_l1 != 0)))) || (((p4_l1 != 0) && ( !(p4_l0 != 0))) || ((p4_l0 != 0) && (p4_l1 != 0))))) && (((( !(p3_l0 != 0)) && ( !(p3_l1 != 0))) && (((( !(p3_l0 != 0)) && ( !(p3_l1 != 0))) || ((p3_l0 != 0) && ( !(p3_l1 != 0)))) || (((p3_l1 != 0) && ( !(p3_l0 != 0))) || ((p3_l0 != 0) && (p3_l1 != 0))))) && (((( !(p2_l0 != 0)) && ( !(p2_l1 != 0))) && (((( !(p2_l0 != 0)) && ( !(p2_l1 != 0))) || ((p2_l0 != 0) && ( !(p2_l1 != 0)))) || (((p2_l1 != 0) && ( !(p2_l0 != 0))) || ((p2_l0 != 0) && (p2_l1 != 0))))) && (((( !(p1_l0 != 0)) && ( !(p1_l1 != 0))) && (((( !(p1_l0 != 0)) && ( !(p1_l1 != 0))) || ((p1_l0 != 0) && ( !(p1_l1 != 0)))) || (((p1_l1 != 0) && ( !(p1_l0 != 0))) || ((p1_l0 != 0) && (p1_l1 != 0))))) && (((( !(p0_l0 != 0)) && ( !(p0_l1 != 0))) && (((( !(p0_l0 != 0)) && ( !(p0_l1 != 0))) || ((p0_l0 != 0) && ( !(p0_l1 != 0)))) || (((p0_l1 != 0) && ( !(p0_l0 != 0))) || ((p0_l0 != 0) && (p0_l1 != 0))))) && (((((((((((((((((((num0 == 0) && (num1 == 0)) && (num2 == 0)) && (num3 == 0)) && (num4 == 0)) && (((run2 != 0) && (( !(run0 != 0)) && ( !(run1 != 0)))) || ((( !(run2 != 0)) && ((run0 != 0) && (run1 != 0))) || ((( !(run2 != 0)) && ((run1 != 0) && ( !(run0 != 0)))) || ((( !(run2 != 0)) && (( !(run0 != 0)) && ( !(run1 != 0)))) || (( !(run2 != 0)) && ((run0 != 0) && ( !(run1 != 0))))))))) && (num0 <= max_num)) && (num1 <= max_num)) && (num2 <= max_num)) && (num3 <= max_num)) && (num4 <= max_num)) && (((((num0 == max_num) || (num1 == max_num)) || (num2 == max_num)) || (num3 == max_num)) || (num4 == max_num))) && ((((((num0 == 0) && (num1 == 0)) && (num2 == 0)) && (num3 == 0)) && (num4 == 0)) == (min_num == 0))) && ((num0 <= 0) || (min_num <= num0))) && ((num1 <= 0) || (min_num <= num1))) && ((num2 <= 0) || (min_num <= num2))) && ((num3 <= 0) || (min_num <= num3))) && ((num4 <= 0) || (min_num <= num4))) && (((num3 == min_num) || ((num2 == min_num) || ((num0 == min_num) || (num1 == min_num)))) || (num4 == min_num))))))));
  while (__ok) {
    _x_p3_l1 = __VERIFIER_nondet_bool();
    _x_p3_l0 = __VERIFIER_nondet_bool();
    _x_p2_l1 = __VERIFIER_nondet_bool();
    _x_p2_l0 = __VERIFIER_nondet_bool();
    _x_p1_l1 = __VERIFIER_nondet_bool();
    _x_min_num = __VERIFIER_nondet_int();
    _x_max_num = __VERIFIER_nondet_int();
    _x_run0 = __VERIFIER_nondet_bool();
    _x_run1 = __VERIFIER_nondet_bool();
    _x_run2 = __VERIFIER_nondet_bool();
    _x_p0_l0 = __VERIFIER_nondet_bool();
    _x_num0 = __VERIFIER_nondet_int();
    _x_p4_l0 = __VERIFIER_nondet_bool();
    _x_num1 = __VERIFIER_nondet_int();
    _x_p1_l0 = __VERIFIER_nondet_bool();
    _x_p4_l1 = __VERIFIER_nondet_bool();
    _x_num2 = __VERIFIER_nondet_int();
    _x_num3 = __VERIFIER_nondet_int();
    _x_num4 = __VERIFIER_nondet_int();
    _x_p0_l1 = __VERIFIER_nondet_bool();

    __ok = ((((((((((( !(_x_p4_l0 != 0)) && ( !(_x_p4_l1 != 0))) || ((_x_p4_l0 != 0) && ( !(_x_p4_l1 != 0)))) || (((_x_p4_l1 != 0) && ( !(_x_p4_l0 != 0))) || ((_x_p4_l0 != 0) && (_x_p4_l1 != 0)))) && (((run2 != 0) && (( !(run0 != 0)) && ( !(run1 != 0)))) || ((((p4_l0 != 0) == (_x_p4_l0 != 0)) && ((p4_l1 != 0) == (_x_p4_l1 != 0))) && (num4 == _x_num4)))) && ((((_x_p4_l0 != 0) && ( !(_x_p4_l1 != 0))) && ((_x_num4 + (-1 * max_num)) == 1)) || ( !(((run2 != 0) && (( !(run0 != 0)) && ( !(run1 != 0)))) && (( !(p4_l0 != 0)) && ( !(p4_l1 != 0))))))) && (((num4 == _x_num4) && (((_x_p4_l0 != 0) && ( !(_x_p4_l1 != 0))) || ((_x_p4_l1 != 0) && ( !(_x_p4_l0 != 0))))) || ( !(((run2 != 0) && (( !(run0 != 0)) && ( !(run1 != 0)))) && ((p4_l0 != 0) && ( !(p4_l1 != 0))))))) && (( !(((run2 != 0) && (( !(run0 != 0)) && ( !(run1 != 0)))) && ((p4_l0 != 0) && ( !(p4_l1 != 0))))) || (((_x_p4_l1 != 0) && ( !(_x_p4_l0 != 0))) == ((( !(num2 == min_num)) && (( !(num1 == min_num)) && (( !(num0 == min_num)) && (num4 <= min_num)))) && ( !(num3 == min_num)))))) && (((num4 == _x_num4) && (((_x_p4_l1 != 0) && ( !(_x_p4_l0 != 0))) || ((_x_p4_l0 != 0) && (_x_p4_l1 != 0)))) || ( !(((run2 != 0) && (( !(run0 != 0)) && ( !(run1 != 0)))) && ((p4_l1 != 0) && ( !(p4_l0 != 0))))))) && (((( !(_x_p4_l0 != 0)) && ( !(_x_p4_l1 != 0))) && (num4 == _x_num4)) || ( !(((run2 != 0) && (( !(run0 != 0)) && ( !(run1 != 0)))) && ((p4_l0 != 0) && (p4_l1 != 0)))))) && ((((((((((( !(_x_p3_l0 != 0)) && ( !(_x_p3_l1 != 0))) || ((_x_p3_l0 != 0) && ( !(_x_p3_l1 != 0)))) || (((_x_p3_l1 != 0) && ( !(_x_p3_l0 != 0))) || ((_x_p3_l0 != 0) && (_x_p3_l1 != 0)))) && ((( !(run2 != 0)) && ((run0 != 0) && (run1 != 0))) || ((((p3_l0 != 0) == (_x_p3_l0 != 0)) && ((p3_l1 != 0) == (_x_p3_l1 != 0))) && (num3 == _x_num3)))) && ((((_x_p3_l0 != 0) && ( !(_x_p3_l1 != 0))) && ((_x_num3 + (-1 * max_num)) == 1)) || ( !((( !(run2 != 0)) && ((run0 != 0) && (run1 != 0))) && (( !(p3_l0 != 0)) && ( !(p3_l1 != 0))))))) && (((num3 == _x_num3) && (((_x_p3_l0 != 0) && ( !(_x_p3_l1 != 0))) || ((_x_p3_l1 != 0) && ( !(_x_p3_l0 != 0))))) || ( !((( !(run2 != 0)) && ((run0 != 0) && (run1 != 0))) && ((p3_l0 != 0) && ( !(p3_l1 != 0))))))) && (( !((( !(run2 != 0)) && ((run0 != 0) && (run1 != 0))) && ((p3_l0 != 0) && ( !(p3_l1 != 0))))) || (((_x_p3_l1 != 0) && ( !(_x_p3_l0 != 0))) == ((( !(num1 == min_num)) && (( !(num0 == min_num)) && (num3 <= min_num))) && ( !(num2 == min_num)))))) && (((num3 == _x_num3) && (((_x_p3_l1 != 0) && ( !(_x_p3_l0 != 0))) || ((_x_p3_l0 != 0) && (_x_p3_l1 != 0)))) || ( !((( !(run2 != 0)) && ((run0 != 0) && (run1 != 0))) && ((p3_l1 != 0) && ( !(p3_l0 != 0))))))) && (((( !(_x_p3_l0 != 0)) && ( !(_x_p3_l1 != 0))) && (num3 == _x_num3)) || ( !((( !(run2 != 0)) && ((run0 != 0) && (run1 != 0))) && ((p3_l0 != 0) && (p3_l1 != 0)))))) && ((((((((((( !(_x_p2_l0 != 0)) && ( !(_x_p2_l1 != 0))) || ((_x_p2_l0 != 0) && ( !(_x_p2_l1 != 0)))) || (((_x_p2_l1 != 0) && ( !(_x_p2_l0 != 0))) || ((_x_p2_l0 != 0) && (_x_p2_l1 != 0)))) && ((( !(run2 != 0)) && ((run1 != 0) && ( !(run0 != 0)))) || ((((p2_l0 != 0) == (_x_p2_l0 != 0)) && ((p2_l1 != 0) == (_x_p2_l1 != 0))) && (num2 == _x_num2)))) && ((((_x_p2_l0 != 0) && ( !(_x_p2_l1 != 0))) && ((_x_num2 + (-1 * max_num)) == 1)) || ( !((( !(run2 != 0)) && ((run1 != 0) && ( !(run0 != 0)))) && (( !(p2_l0 != 0)) && ( !(p2_l1 != 0))))))) && (((num2 == _x_num2) && (((_x_p2_l0 != 0) && ( !(_x_p2_l1 != 0))) || ((_x_p2_l1 != 0) && ( !(_x_p2_l0 != 0))))) || ( !((( !(run2 != 0)) && ((run1 != 0) && ( !(run0 != 0)))) && ((p2_l0 != 0) && ( !(p2_l1 != 0))))))) && (( !((( !(run2 != 0)) && ((run1 != 0) && ( !(run0 != 0)))) && ((p2_l0 != 0) && ( !(p2_l1 != 0))))) || (((_x_p2_l1 != 0) && ( !(_x_p2_l0 != 0))) == ((( !(num0 == min_num)) && (num2 <= min_num)) && ( !(num1 == min_num)))))) && (((num2 == _x_num2) && (((_x_p2_l1 != 0) && ( !(_x_p2_l0 != 0))) || ((_x_p2_l0 != 0) && (_x_p2_l1 != 0)))) || ( !((( !(run2 != 0)) && ((run1 != 0) && ( !(run0 != 0)))) && ((p2_l1 != 0) && ( !(p2_l0 != 0))))))) && (((( !(_x_p2_l0 != 0)) && ( !(_x_p2_l1 != 0))) && (num2 == _x_num2)) || ( !((( !(run2 != 0)) && ((run1 != 0) && ( !(run0 != 0)))) && ((p2_l0 != 0) && (p2_l1 != 0)))))) && ((((((((((( !(_x_p1_l0 != 0)) && ( !(_x_p1_l1 != 0))) || ((_x_p1_l0 != 0) && ( !(_x_p1_l1 != 0)))) || (((_x_p1_l1 != 0) && ( !(_x_p1_l0 != 0))) || ((_x_p1_l0 != 0) && (_x_p1_l1 != 0)))) && ((( !(run2 != 0)) && ((run0 != 0) && ( !(run1 != 0)))) || ((((p1_l0 != 0) == (_x_p1_l0 != 0)) && ((p1_l1 != 0) == (_x_p1_l1 != 0))) && (num1 == _x_num1)))) && ((((_x_p1_l0 != 0) && ( !(_x_p1_l1 != 0))) && ((_x_num1 + (-1 * max_num)) == 1)) || ( !((( !(run2 != 0)) && ((run0 != 0) && ( !(run1 != 0)))) && (( !(p1_l0 != 0)) && ( !(p1_l1 != 0))))))) && (((num1 == _x_num1) && (((_x_p1_l0 != 0) && ( !(_x_p1_l1 != 0))) || ((_x_p1_l1 != 0) && ( !(_x_p1_l0 != 0))))) || ( !((( !(run2 != 0)) && ((run0 != 0) && ( !(run1 != 0)))) && ((p1_l0 != 0) && ( !(p1_l1 != 0))))))) && (( !((( !(run2 != 0)) && ((run0 != 0) && ( !(run1 != 0)))) && ((p1_l0 != 0) && ( !(p1_l1 != 0))))) || (((_x_p1_l1 != 0) && ( !(_x_p1_l0 != 0))) == ((num1 <= min_num) && ( !(num0 == min_num)))))) && (((num1 == _x_num1) && (((_x_p1_l1 != 0) && ( !(_x_p1_l0 != 0))) || ((_x_p1_l0 != 0) && (_x_p1_l1 != 0)))) || ( !((( !(run2 != 0)) && ((run0 != 0) && ( !(run1 != 0)))) && ((p1_l1 != 0) && ( !(p1_l0 != 0))))))) && (((( !(_x_p1_l0 != 0)) && ( !(_x_p1_l1 != 0))) && (num1 == _x_num1)) || ( !((( !(run2 != 0)) && ((run0 != 0) && ( !(run1 != 0)))) && ((p1_l0 != 0) && (p1_l1 != 0)))))) && ((((((((((( !(_x_p0_l0 != 0)) && ( !(_x_p0_l1 != 0))) || ((_x_p0_l0 != 0) && ( !(_x_p0_l1 != 0)))) || (((_x_p0_l1 != 0) && ( !(_x_p0_l0 != 0))) || ((_x_p0_l0 != 0) && (_x_p0_l1 != 0)))) && ((( !(run2 != 0)) && (( !(run0 != 0)) && ( !(run1 != 0)))) || ((((p0_l0 != 0) == (_x_p0_l0 != 0)) && ((p0_l1 != 0) == (_x_p0_l1 != 0))) && (num0 == _x_num0)))) && ((((_x_p0_l0 != 0) && ( !(_x_p0_l1 != 0))) && ((_x_num0 + (-1 * max_num)) == 1)) || ( !((( !(run2 != 0)) && (( !(run0 != 0)) && ( !(run1 != 0)))) && (( !(p0_l0 != 0)) && ( !(p0_l1 != 0))))))) && (((num0 == _x_num0) && (((_x_p0_l0 != 0) && ( !(_x_p0_l1 != 0))) || ((_x_p0_l1 != 0) && ( !(_x_p0_l0 != 0))))) || ( !((( !(run2 != 0)) && (( !(run0 != 0)) && ( !(run1 != 0)))) && ((p0_l0 != 0) && ( !(p0_l1 != 0))))))) && (( !((( !(run2 != 0)) && (( !(run0 != 0)) && ( !(run1 != 0)))) && ((p0_l0 != 0) && ( !(p0_l1 != 0))))) || (((_x_p0_l1 != 0) && ( !(_x_p0_l0 != 0))) == (num0 <= min_num)))) && (((num0 == _x_num0) && (((_x_p0_l1 != 0) && ( !(_x_p0_l0 != 0))) || ((_x_p0_l0 != 0) && (_x_p0_l1 != 0)))) || ( !((( !(run2 != 0)) && (( !(run0 != 0)) && ( !(run1 != 0)))) && ((p0_l1 != 0) && ( !(p0_l0 != 0))))))) && (((( !(_x_p0_l0 != 0)) && ( !(_x_p0_l1 != 0))) && (num0 == _x_num0)) || ( !((( !(run2 != 0)) && (( !(run0 != 0)) && ( !(run1 != 0)))) && ((p0_l0 != 0) && (p0_l1 != 0)))))) && ((((((((((((((((_x_run2 != 0) && (( !(_x_run0 != 0)) && ( !(_x_run1 != 0)))) || ((( !(_x_run2 != 0)) && ((_x_run0 != 0) && (_x_run1 != 0))) || ((( !(_x_run2 != 0)) && ((_x_run1 != 0) && ( !(_x_run0 != 0)))) || ((( !(_x_run2 != 0)) && (( !(_x_run0 != 0)) && ( !(_x_run1 != 0)))) || (( !(_x_run2 != 0)) && ((_x_run0 != 0) && ( !(_x_run1 != 0)))))))) && (_x_num0 <= _x_max_num)) && (_x_num1 <= _x_max_num)) && (_x_num2 <= _x_max_num)) && (_x_num3 <= _x_max_num)) && (_x_num4 <= _x_max_num)) && (((((_x_num0 == _x_max_num) || (_x_num1 == _x_max_num)) || (_x_num2 == _x_max_num)) || (_x_num3 == _x_max_num)) || (_x_num4 == _x_max_num))) && ((((((_x_num0 == 0) && (_x_num1 == 0)) && (_x_num2 == 0)) && (_x_num3 == 0)) && (_x_num4 == 0)) == (_x_min_num == 0))) && ((_x_num0 <= 0) || (_x_min_num <= _x_num0))) && ((_x_num1 <= 0) || (_x_min_num <= _x_num1))) && ((_x_num2 <= 0) || (_x_min_num <= _x_num2))) && ((_x_num3 <= 0) || (_x_min_num <= _x_num3))) && ((_x_num4 <= 0) || (_x_min_num <= _x_num4))) && (((((_x_num0 == _x_min_num) || (_x_num1 == _x_min_num)) || (_x_num2 == _x_min_num)) || (_x_num3 == _x_min_num)) || (_x_num4 == _x_min_num))))))));
    p3_l1 = _x_p3_l1;
    p3_l0 = _x_p3_l0;
    p2_l1 = _x_p2_l1;
    p2_l0 = _x_p2_l0;
    p1_l1 = _x_p1_l1;
    min_num = _x_min_num;
    max_num = _x_max_num;
    run0 = _x_run0;
    run1 = _x_run1;
    run2 = _x_run2;
    p0_l0 = _x_p0_l0;
    num0 = _x_num0;
    p4_l0 = _x_p4_l0;
    num1 = _x_num1;
    p1_l0 = _x_p1_l0;
    p4_l1 = _x_p4_l1;
    num2 = _x_num2;
    num3 = _x_num3;
    num4 = _x_num4;
    p0_l1 = _x_p0_l1;

  }
}
