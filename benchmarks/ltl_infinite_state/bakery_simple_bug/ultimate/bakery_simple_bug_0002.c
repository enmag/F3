//@ ltl invariant negative: ( ([] (<> AP((num0 == 0)))) || (! ([] ( (<> ( (! AP((p0_l0 != 0))) && (! AP((p0_l1 != 0))))) && (<> (! ( (! AP((p0_l0 != 0))) && (! AP((p0_l1 != 0))))))))));

extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);

char __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}


char p1_l1, _x_p1_l1;
char p0_l1, _x_p0_l1;
char p0_l0, _x_p0_l0;
int num1, _x_num1;
int num0, _x_num0;
char p1_l0, _x_p1_l0;
char run0, _x_run0;
int max_num, _x_max_num;
int min_num, _x_min_num;

int main()
{
  p1_l1 = __VERIFIER_nondet_bool();
  p0_l1 = __VERIFIER_nondet_bool();
  p0_l0 = __VERIFIER_nondet_bool();
  num1 = __VERIFIER_nondet_int();
  num0 = __VERIFIER_nondet_int();
  p1_l0 = __VERIFIER_nondet_bool();
  run0 = __VERIFIER_nondet_bool();
  max_num = __VERIFIER_nondet_int();
  min_num = __VERIFIER_nondet_int();

  int __ok = (((( !(p1_l0 != 0)) && ( !(p1_l1 != 0))) && (((( !(p1_l0 != 0)) && ( !(p1_l1 != 0))) || ((p1_l0 != 0) && ( !(p1_l1 != 0)))) || (((p1_l1 != 0) && ( !(p1_l0 != 0))) || ((p1_l0 != 0) && (p1_l1 != 0))))) && (((( !(p0_l0 != 0)) && ( !(p0_l1 != 0))) && (((( !(p0_l0 != 0)) && ( !(p0_l1 != 0))) || ((p0_l0 != 0) && ( !(p0_l1 != 0)))) || (((p0_l1 != 0) && ( !(p0_l0 != 0))) || ((p0_l0 != 0) && (p0_l1 != 0))))) && (((((((((num0 == 0) && (num1 == 0)) && (num0 <= max_num)) && (num1 <= max_num)) && ((num0 == max_num) || (num1 == max_num))) && (((num0 == 0) && (num1 == 0)) == (min_num == 0))) && ((num0 <= 0) || (min_num <= num0))) && ((num1 <= 0) || (min_num <= num1))) && ((num0 == min_num) || (num1 == min_num)))));
  while (__ok) {
    _x_p1_l1 = __VERIFIER_nondet_bool();
    _x_p0_l1 = __VERIFIER_nondet_bool();
    _x_p0_l0 = __VERIFIER_nondet_bool();
    _x_num1 = __VERIFIER_nondet_int();
    _x_num0 = __VERIFIER_nondet_int();
    _x_p1_l0 = __VERIFIER_nondet_bool();
    _x_run0 = __VERIFIER_nondet_bool();
    _x_max_num = __VERIFIER_nondet_int();
    _x_min_num = __VERIFIER_nondet_int();

    __ok = ((((((((((( !(_x_p1_l0 != 0)) && ( !(_x_p1_l1 != 0))) || ((_x_p1_l0 != 0) && ( !(_x_p1_l1 != 0)))) || (((_x_p1_l1 != 0) && ( !(_x_p1_l0 != 0))) || ((_x_p1_l0 != 0) && (_x_p1_l1 != 0)))) && ((run0 != 0) || ((((p1_l0 != 0) == (_x_p1_l0 != 0)) && ((p1_l1 != 0) == (_x_p1_l1 != 0))) && (num1 == _x_num1)))) && ((((_x_p1_l0 != 0) && ( !(_x_p1_l1 != 0))) && ((_x_num1 + (-1 * max_num)) == 1)) || ( !((run0 != 0) && (( !(p1_l0 != 0)) && ( !(p1_l1 != 0))))))) && (((num1 == _x_num1) && (((_x_p1_l0 != 0) && ( !(_x_p1_l1 != 0))) || ((_x_p1_l1 != 0) && ( !(_x_p1_l0 != 0))))) || ( !((run0 != 0) && ((p1_l0 != 0) && ( !(p1_l1 != 0))))))) && (( !((run0 != 0) && ((p1_l0 != 0) && ( !(p1_l1 != 0))))) || (((_x_p1_l1 != 0) && ( !(_x_p1_l0 != 0))) == ((num1 <= min_num) && ( !(num0 == min_num)))))) && (((num1 == _x_num1) && (((_x_p1_l1 != 0) && ( !(_x_p1_l0 != 0))) || ((_x_p1_l0 != 0) && (_x_p1_l1 != 0)))) || ( !((run0 != 0) && ((p1_l1 != 0) && ( !(p1_l0 != 0))))))) && (((( !(_x_p1_l0 != 0)) && ( !(_x_p1_l1 != 0))) && (num1 == _x_num1)) || ( !((run0 != 0) && ((p1_l0 != 0) && (p1_l1 != 0)))))) && ((((((((((( !(_x_p0_l0 != 0)) && ( !(_x_p0_l1 != 0))) || ((_x_p0_l0 != 0) && ( !(_x_p0_l1 != 0)))) || (((_x_p0_l1 != 0) && ( !(_x_p0_l0 != 0))) || ((_x_p0_l0 != 0) && (_x_p0_l1 != 0)))) && (( !(run0 != 0)) || ((((p0_l0 != 0) == (_x_p0_l0 != 0)) && ((p0_l1 != 0) == (_x_p0_l1 != 0))) && (num0 == _x_num0)))) && ((((_x_p0_l0 != 0) && ( !(_x_p0_l1 != 0))) && ((_x_num0 + (-1 * max_num)) == 1)) || ( !(( !(run0 != 0)) && (( !(p0_l0 != 0)) && ( !(p0_l1 != 0))))))) && (((num0 == _x_num0) && (((_x_p0_l0 != 0) && ( !(_x_p0_l1 != 0))) || ((_x_p0_l1 != 0) && ( !(_x_p0_l0 != 0))))) || ( !(( !(run0 != 0)) && ((p0_l0 != 0) && ( !(p0_l1 != 0))))))) && (( !(( !(run0 != 0)) && ((p0_l0 != 0) && ( !(p0_l1 != 0))))) || (((_x_p0_l1 != 0) && ( !(_x_p0_l0 != 0))) == (num0 <= min_num)))) && (((num0 == _x_num0) && (((_x_p0_l1 != 0) && ( !(_x_p0_l0 != 0))) || ((_x_p0_l0 != 0) && (_x_p0_l1 != 0)))) || ( !(( !(run0 != 0)) && ((p0_l1 != 0) && ( !(p0_l0 != 0))))))) && (((( !(_x_p0_l0 != 0)) && ( !(_x_p0_l1 != 0))) && (num0 == _x_num0)) || ( !(( !(run0 != 0)) && ((p0_l0 != 0) && (p0_l1 != 0)))))) && (((((((_x_num0 <= _x_max_num) && (_x_num1 <= _x_max_num)) && ((_x_num0 == _x_max_num) || (_x_num1 == _x_max_num))) && (((_x_num0 == 0) && (_x_num1 == 0)) == (_x_min_num == 0))) && ((_x_num0 <= 0) || (_x_min_num <= _x_num0))) && ((_x_num1 <= 0) || (_x_min_num <= _x_num1))) && ((_x_num0 == _x_min_num) || (_x_num1 == _x_min_num)))));
    p1_l1 = _x_p1_l1;
    p0_l1 = _x_p0_l1;
    p0_l0 = _x_p0_l0;
    num1 = _x_num1;
    num0 = _x_num0;
    p1_l0 = _x_p1_l0;
    run0 = _x_run0;
    max_num = _x_max_num;
    min_num = _x_min_num;

  }
}
