//@ ltl invariant negative: ( ( ([] (<> ( (! AP((s0_l0 != 0))) && (! AP((s0_l1 != 0)))))) || (! ([] (<> ( AP((s0_l1 != 0)) && (! AP((s0_l0 != 0)))))))) || (! ([] (<> AP((1.0 <= _diverge_delta))))));

extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);

char __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}


float _diverge_delta, _x__diverge_delta;
char s2_l1, _x_s2_l1;
char s2_l0, _x_s2_l0;
char s2_evt2, _x_s2_evt2;
char s0_evt0, _x_s0_evt0;
char bus_l1, _x_bus_l1;
char bus_evt2, _x_bus_evt2;
float s0_backoff, _x_s0_backoff;
float s0_lambda, _x_s0_lambda;
char s1_evt0, _x_s1_evt0;
float delta, _x_delta;
char s2_evt1, _x_s2_evt1;
float bus_x, _x_bus_x;
float s1_lambda, _x_s1_lambda;
float s0_x, _x_s0_x;
char s2_evt0, _x_s2_evt0;
int bus_j, _x_bus_j;
float s1_x, _x_s1_x;
char s0_evt1, _x_s0_evt1;
char s0_evt2, _x_s0_evt2;
char s0_l0, _x_s0_l0;
float s2_lambda, _x_s2_lambda;
char s0_l1, _x_s0_l1;
float s2_backoff, _x_s2_backoff;
int bus_cd_id, _x_bus_cd_id;
float s1_backoff, _x_s1_backoff;
char bus_evt0, _x_bus_evt0;
char s1_evt1, _x_s1_evt1;
char bus_evt1, _x_bus_evt1;
char s1_evt2, _x_s1_evt2;
char s1_l0, _x_s1_l0;
char bus_l0, _x_bus_l0;
char s1_l1, _x_s1_l1;
float s2_x, _x_s2_x;

int main()
{
  _diverge_delta = __VERIFIER_nondet_float();
  s2_l1 = __VERIFIER_nondet_bool();
  s2_l0 = __VERIFIER_nondet_bool();
  s2_evt2 = __VERIFIER_nondet_bool();
  s0_evt0 = __VERIFIER_nondet_bool();
  bus_l1 = __VERIFIER_nondet_bool();
  bus_evt2 = __VERIFIER_nondet_bool();
  s0_backoff = __VERIFIER_nondet_float();
  s0_lambda = __VERIFIER_nondet_float();
  s1_evt0 = __VERIFIER_nondet_bool();
  delta = __VERIFIER_nondet_float();
  s2_evt1 = __VERIFIER_nondet_bool();
  bus_x = __VERIFIER_nondet_float();
  s1_lambda = __VERIFIER_nondet_float();
  s0_x = __VERIFIER_nondet_float();
  s2_evt0 = __VERIFIER_nondet_bool();
  bus_j = __VERIFIER_nondet_int();
  s1_x = __VERIFIER_nondet_float();
  s0_evt1 = __VERIFIER_nondet_bool();
  s0_evt2 = __VERIFIER_nondet_bool();
  s0_l0 = __VERIFIER_nondet_bool();
  s2_lambda = __VERIFIER_nondet_float();
  s0_l1 = __VERIFIER_nondet_bool();
  s2_backoff = __VERIFIER_nondet_float();
  bus_cd_id = __VERIFIER_nondet_int();
  s1_backoff = __VERIFIER_nondet_float();
  bus_evt0 = __VERIFIER_nondet_bool();
  s1_evt1 = __VERIFIER_nondet_bool();
  bus_evt1 = __VERIFIER_nondet_bool();
  s1_evt2 = __VERIFIER_nondet_bool();
  s1_l0 = __VERIFIER_nondet_bool();
  bus_l0 = __VERIFIER_nondet_bool();
  s1_l1 = __VERIFIER_nondet_bool();
  s2_x = __VERIFIER_nondet_float();

  int __ok = ((((((((( !(s2_l0 != 0)) && ( !(s2_l1 != 0))) && (s2_x == 0.0)) && ((( !(s2_evt2 != 0)) && ((s2_evt0 != 0) && ( !(s2_evt1 != 0)))) || (((( !(s2_evt2 != 0)) && (( !(s2_evt0 != 0)) && ( !(s2_evt1 != 0)))) || ((s2_evt2 != 0) && (( !(s2_evt0 != 0)) && ( !(s2_evt1 != 0))))) || ((( !(s2_evt2 != 0)) && ((s2_evt1 != 0) && ( !(s2_evt0 != 0)))) || ((s2_evt2 != 0) && ((s2_evt1 != 0) && ( !(s2_evt0 != 0)))))))) && ((( !(s2_l0 != 0)) && ( !(s2_l1 != 0))) || (((s2_l1 != 0) && ( !(s2_l0 != 0))) || ((s2_l0 != 0) && ( !(s2_l1 != 0)))))) && (13.0 <= s2_backoff)) && (( !(s2_lambda <= 0.0)) && ((s2_x <= s2_lambda) || ( !((s2_l1 != 0) && ( !(s2_l0 != 0))))))) && (((((((( !(s1_l0 != 0)) && ( !(s1_l1 != 0))) && (s1_x == 0.0)) && ((( !(s1_evt2 != 0)) && ((s1_evt0 != 0) && ( !(s1_evt1 != 0)))) || (((( !(s1_evt2 != 0)) && (( !(s1_evt0 != 0)) && ( !(s1_evt1 != 0)))) || ((s1_evt2 != 0) && (( !(s1_evt0 != 0)) && ( !(s1_evt1 != 0))))) || ((( !(s1_evt2 != 0)) && ((s1_evt1 != 0) && ( !(s1_evt0 != 0)))) || ((s1_evt2 != 0) && ((s1_evt1 != 0) && ( !(s1_evt0 != 0)))))))) && ((( !(s1_l0 != 0)) && ( !(s1_l1 != 0))) || (((s1_l1 != 0) && ( !(s1_l0 != 0))) || ((s1_l0 != 0) && ( !(s1_l1 != 0)))))) && (13.0 <= s1_backoff)) && (( !(s1_lambda <= 0.0)) && ((s1_x <= s1_lambda) || ( !((s1_l1 != 0) && ( !(s1_l0 != 0))))))) && (((((((( !(s0_l0 != 0)) && ( !(s0_l1 != 0))) && (s0_x == 0.0)) && ((( !(s0_evt2 != 0)) && ((s0_evt0 != 0) && ( !(s0_evt1 != 0)))) || (((( !(s0_evt2 != 0)) && (( !(s0_evt0 != 0)) && ( !(s0_evt1 != 0)))) || ((s0_evt2 != 0) && (( !(s0_evt0 != 0)) && ( !(s0_evt1 != 0))))) || ((( !(s0_evt2 != 0)) && ((s0_evt1 != 0) && ( !(s0_evt0 != 0)))) || ((s0_evt2 != 0) && ((s0_evt1 != 0) && ( !(s0_evt0 != 0)))))))) && ((( !(s0_l0 != 0)) && ( !(s0_l1 != 0))) || (((s0_l1 != 0) && ( !(s0_l0 != 0))) || ((s0_l0 != 0) && ( !(s0_l1 != 0)))))) && (13.0 <= s0_backoff)) && (( !(s0_lambda <= 0.0)) && ((s0_x <= s0_lambda) || ( !((s0_l1 != 0) && ( !(s0_l0 != 0))))))) && (((((( !(bus_l0 != 0)) && ( !(bus_l1 != 0))) && (((( !(bus_evt2 != 0)) && (( !(bus_evt0 != 0)) && ( !(bus_evt1 != 0)))) || ((((bus_evt2 != 0) && (( !(bus_evt0 != 0)) && ( !(bus_evt1 != 0)))) || (( !(bus_evt2 != 0)) && ((bus_evt1 != 0) && ( !(bus_evt0 != 0))))) || (((bus_evt2 != 0) && ((bus_evt1 != 0) && ( !(bus_evt0 != 0)))) || (( !(bus_evt2 != 0)) && ((bus_evt0 != 0) && ( !(bus_evt1 != 0))))))) && (((( !(bus_l0 != 0)) && ( !(bus_l1 != 0))) || ((bus_l1 != 0) && ( !(bus_l0 != 0)))) || (((bus_l0 != 0) && ( !(bus_l1 != 0))) || ((bus_l0 != 0) && (bus_l1 != 0)))))) && ((bus_j == 0) && (bus_x == 0.0))) && ((( !(13.0 <= bus_x)) || ( !((bus_l0 != 0) && ( !(bus_l1 != 0))))) && ((delta == 0.0) || ( !((bus_l0 != 0) && (bus_l1 != 0)))))) && (0.0 <= delta))))) && (delta == _diverge_delta));
  while (__ok) {
    _x__diverge_delta = __VERIFIER_nondet_float();
    _x_s2_l1 = __VERIFIER_nondet_bool();
    _x_s2_l0 = __VERIFIER_nondet_bool();
    _x_s2_evt2 = __VERIFIER_nondet_bool();
    _x_s0_evt0 = __VERIFIER_nondet_bool();
    _x_bus_l1 = __VERIFIER_nondet_bool();
    _x_bus_evt2 = __VERIFIER_nondet_bool();
    _x_s0_backoff = __VERIFIER_nondet_float();
    _x_s0_lambda = __VERIFIER_nondet_float();
    _x_s1_evt0 = __VERIFIER_nondet_bool();
    _x_delta = __VERIFIER_nondet_float();
    _x_s2_evt1 = __VERIFIER_nondet_bool();
    _x_bus_x = __VERIFIER_nondet_float();
    _x_s1_lambda = __VERIFIER_nondet_float();
    _x_s0_x = __VERIFIER_nondet_float();
    _x_s2_evt0 = __VERIFIER_nondet_bool();
    _x_bus_j = __VERIFIER_nondet_int();
    _x_s1_x = __VERIFIER_nondet_float();
    _x_s0_evt1 = __VERIFIER_nondet_bool();
    _x_s0_evt2 = __VERIFIER_nondet_bool();
    _x_s0_l0 = __VERIFIER_nondet_bool();
    _x_s2_lambda = __VERIFIER_nondet_float();
    _x_s0_l1 = __VERIFIER_nondet_bool();
    _x_s2_backoff = __VERIFIER_nondet_float();
    _x_bus_cd_id = __VERIFIER_nondet_int();
    _x_s1_backoff = __VERIFIER_nondet_float();
    _x_bus_evt0 = __VERIFIER_nondet_bool();
    _x_s1_evt1 = __VERIFIER_nondet_bool();
    _x_bus_evt1 = __VERIFIER_nondet_bool();
    _x_s1_evt2 = __VERIFIER_nondet_bool();
    _x_s1_l0 = __VERIFIER_nondet_bool();
    _x_bus_l0 = __VERIFIER_nondet_bool();
    _x_s1_l1 = __VERIFIER_nondet_bool();
    _x_s2_x = __VERIFIER_nondet_float();

    __ok = ((((((((((((((((((((((( !(_x_s2_evt2 != 0)) && ((_x_s2_evt0 != 0) && ( !(_x_s2_evt1 != 0)))) || (((( !(_x_s2_evt2 != 0)) && (( !(_x_s2_evt0 != 0)) && ( !(_x_s2_evt1 != 0)))) || ((_x_s2_evt2 != 0) && (( !(_x_s2_evt0 != 0)) && ( !(_x_s2_evt1 != 0))))) || ((( !(_x_s2_evt2 != 0)) && ((_x_s2_evt1 != 0) && ( !(_x_s2_evt0 != 0)))) || ((_x_s2_evt2 != 0) && ((_x_s2_evt1 != 0) && ( !(_x_s2_evt0 != 0))))))) && ((( !(_x_s2_l0 != 0)) && ( !(_x_s2_l1 != 0))) || (((_x_s2_l1 != 0) && ( !(_x_s2_l0 != 0))) || ((_x_s2_l0 != 0) && ( !(_x_s2_l1 != 0)))))) && (13.0 <= _x_s2_backoff)) && (( !(_x_s2_lambda <= 0.0)) && ((_x_s2_x <= _x_s2_lambda) || ( !((_x_s2_l1 != 0) && ( !(_x_s2_l0 != 0))))))) && ((((((s2_l0 != 0) == (_x_s2_l0 != 0)) && ((s2_l1 != 0) == (_x_s2_l1 != 0))) && (s2_lambda == _x_s2_lambda)) && (((delta + (s2_x + (-1.0 * _x_s2_x))) == 0.0) && (s2_backoff == _x_s2_backoff))) || ( !(( !(delta <= 0.0)) || (( !(s2_evt2 != 0)) && (( !(s2_evt0 != 0)) && ( !(s2_evt1 != 0)))))))) && (((((_x_s2_l0 != 0) && ( !(_x_s2_l1 != 0))) || ((( !(_x_s2_l0 != 0)) && ( !(_x_s2_l1 != 0))) || ((_x_s2_l1 != 0) && ( !(_x_s2_l0 != 0))))) && ((s2_backoff == _x_s2_backoff) && (_x_s2_x == 0.0))) || ( !((( !(s2_l0 != 0)) && ( !(s2_l1 != 0))) && ((delta == 0.0) && ( !(( !(s2_evt2 != 0)) && (( !(s2_evt0 != 0)) && ( !(s2_evt1 != 0)))))))))) && (((( !(s2_evt2 != 0)) && ((s2_evt0 != 0) && ( !(s2_evt1 != 0)))) && (s2_lambda == _x_s2_lambda)) || ( !((( !(_x_s2_l0 != 0)) && ( !(_x_s2_l1 != 0))) && ((( !(s2_l0 != 0)) && ( !(s2_l1 != 0))) && ((delta == 0.0) && ( !(( !(s2_evt2 != 0)) && (( !(s2_evt0 != 0)) && ( !(s2_evt1 != 0))))))))))) && (((s2_evt2 != 0) && (( !(s2_evt0 != 0)) && ( !(s2_evt1 != 0)))) || ( !(((_x_s2_l1 != 0) && ( !(_x_s2_l0 != 0))) && ((( !(s2_l0 != 0)) && ( !(s2_l1 != 0))) && ((delta == 0.0) && ( !(( !(s2_evt2 != 0)) && (( !(s2_evt0 != 0)) && ( !(s2_evt1 != 0))))))))))) && (((s2_lambda == _x_s2_lambda) && (((s2_evt2 != 0) && ((s2_evt1 != 0) && ( !(s2_evt0 != 0)))) || (( !(s2_evt2 != 0)) && ((s2_evt0 != 0) && ( !(s2_evt1 != 0)))))) || ( !(((_x_s2_l0 != 0) && ( !(_x_s2_l1 != 0))) && ((( !(s2_l0 != 0)) && ( !(s2_l1 != 0))) && ((delta == 0.0) && ( !(( !(s2_evt2 != 0)) && (( !(s2_evt0 != 0)) && ( !(s2_evt1 != 0))))))))))) && ((((s2_lambda == _x_s2_lambda) && (_x_s2_x == 0.0)) && ((( !(_x_s2_l0 != 0)) && ( !(_x_s2_l1 != 0))) || ((_x_s2_l0 != 0) && ( !(_x_s2_l1 != 0))))) || ( !(((s2_l1 != 0) && ( !(s2_l0 != 0))) && ((delta == 0.0) && ( !(( !(s2_evt2 != 0)) && (( !(s2_evt0 != 0)) && ( !(s2_evt1 != 0)))))))))) && (((s2_lambda <= s2_x) && ((( !(s2_evt2 != 0)) && ((s2_evt1 != 0) && ( !(s2_evt0 != 0)))) && (_x_s2_backoff <= s2_backoff))) || ( !((( !(_x_s2_l0 != 0)) && ( !(_x_s2_l1 != 0))) && (((s2_l1 != 0) && ( !(s2_l0 != 0))) && ((delta == 0.0) && ( !(( !(s2_evt2 != 0)) && (( !(s2_evt0 != 0)) && ( !(s2_evt1 != 0))))))))))) && (((( !(s2_evt2 != 0)) && ((s2_evt0 != 0) && ( !(s2_evt1 != 0)))) && ((s2_backoff + (-1.0 * _x_s2_backoff)) <= -1.0)) || ( !(((_x_s2_l0 != 0) && ( !(_x_s2_l1 != 0))) && (((s2_l1 != 0) && ( !(s2_l0 != 0))) && ((delta == 0.0) && ( !(( !(s2_evt2 != 0)) && (( !(s2_evt0 != 0)) && ( !(s2_evt1 != 0))))))))))) && (((s2_lambda == _x_s2_lambda) && ((((_x_s2_l1 != 0) && ( !(_x_s2_l0 != 0))) || ((_x_s2_l0 != 0) && ( !(_x_s2_l1 != 0)))) && ((s2_backoff == _x_s2_backoff) && (_x_s2_x == 0.0)))) || ( !(((s2_l0 != 0) && ( !(s2_l1 != 0))) && ((delta == 0.0) && ( !(( !(s2_evt2 != 0)) && (( !(s2_evt0 != 0)) && ( !(s2_evt1 != 0)))))))))) && ((( !(s2_evt2 != 0)) && ((s2_evt0 != 0) && ( !(s2_evt1 != 0)))) || ( !(((_x_s2_l0 != 0) && ( !(_x_s2_l1 != 0))) && (((s2_l0 != 0) && ( !(s2_l1 != 0))) && ((delta == 0.0) && ( !(( !(s2_evt2 != 0)) && (( !(s2_evt0 != 0)) && ( !(s2_evt1 != 0))))))))))) && ((((s2_evt2 != 0) && (( !(s2_evt0 != 0)) && ( !(s2_evt1 != 0)))) && (s2_backoff <= s2_x)) || ( !(((_x_s2_l1 != 0) && ( !(_x_s2_l0 != 0))) && (((s2_l0 != 0) && ( !(s2_l1 != 0))) && ((delta == 0.0) && ( !(( !(s2_evt2 != 0)) && (( !(s2_evt0 != 0)) && ( !(s2_evt1 != 0))))))))))) && (((((((((((((((((( !(_x_s1_evt2 != 0)) && ((_x_s1_evt0 != 0) && ( !(_x_s1_evt1 != 0)))) || (((( !(_x_s1_evt2 != 0)) && (( !(_x_s1_evt0 != 0)) && ( !(_x_s1_evt1 != 0)))) || ((_x_s1_evt2 != 0) && (( !(_x_s1_evt0 != 0)) && ( !(_x_s1_evt1 != 0))))) || ((( !(_x_s1_evt2 != 0)) && ((_x_s1_evt1 != 0) && ( !(_x_s1_evt0 != 0)))) || ((_x_s1_evt2 != 0) && ((_x_s1_evt1 != 0) && ( !(_x_s1_evt0 != 0))))))) && ((( !(_x_s1_l0 != 0)) && ( !(_x_s1_l1 != 0))) || (((_x_s1_l1 != 0) && ( !(_x_s1_l0 != 0))) || ((_x_s1_l0 != 0) && ( !(_x_s1_l1 != 0)))))) && (13.0 <= _x_s1_backoff)) && (( !(_x_s1_lambda <= 0.0)) && ((_x_s1_x <= _x_s1_lambda) || ( !((_x_s1_l1 != 0) && ( !(_x_s1_l0 != 0))))))) && ((((((s1_l0 != 0) == (_x_s1_l0 != 0)) && ((s1_l1 != 0) == (_x_s1_l1 != 0))) && (s1_lambda == _x_s1_lambda)) && (((delta + (s1_x + (-1.0 * _x_s1_x))) == 0.0) && (s1_backoff == _x_s1_backoff))) || ( !(( !(delta <= 0.0)) || (( !(s1_evt2 != 0)) && (( !(s1_evt0 != 0)) && ( !(s1_evt1 != 0)))))))) && (((((_x_s1_l0 != 0) && ( !(_x_s1_l1 != 0))) || ((( !(_x_s1_l0 != 0)) && ( !(_x_s1_l1 != 0))) || ((_x_s1_l1 != 0) && ( !(_x_s1_l0 != 0))))) && ((s1_backoff == _x_s1_backoff) && (_x_s1_x == 0.0))) || ( !((( !(s1_l0 != 0)) && ( !(s1_l1 != 0))) && ((delta == 0.0) && ( !(( !(s1_evt2 != 0)) && (( !(s1_evt0 != 0)) && ( !(s1_evt1 != 0)))))))))) && (((( !(s1_evt2 != 0)) && ((s1_evt0 != 0) && ( !(s1_evt1 != 0)))) && (s1_lambda == _x_s1_lambda)) || ( !((( !(_x_s1_l0 != 0)) && ( !(_x_s1_l1 != 0))) && ((( !(s1_l0 != 0)) && ( !(s1_l1 != 0))) && ((delta == 0.0) && ( !(( !(s1_evt2 != 0)) && (( !(s1_evt0 != 0)) && ( !(s1_evt1 != 0))))))))))) && (((s1_evt2 != 0) && (( !(s1_evt0 != 0)) && ( !(s1_evt1 != 0)))) || ( !(((_x_s1_l1 != 0) && ( !(_x_s1_l0 != 0))) && ((( !(s1_l0 != 0)) && ( !(s1_l1 != 0))) && ((delta == 0.0) && ( !(( !(s1_evt2 != 0)) && (( !(s1_evt0 != 0)) && ( !(s1_evt1 != 0))))))))))) && (((s1_lambda == _x_s1_lambda) && (((s1_evt2 != 0) && ((s1_evt1 != 0) && ( !(s1_evt0 != 0)))) || (( !(s1_evt2 != 0)) && ((s1_evt0 != 0) && ( !(s1_evt1 != 0)))))) || ( !(((_x_s1_l0 != 0) && ( !(_x_s1_l1 != 0))) && ((( !(s1_l0 != 0)) && ( !(s1_l1 != 0))) && ((delta == 0.0) && ( !(( !(s1_evt2 != 0)) && (( !(s1_evt0 != 0)) && ( !(s1_evt1 != 0))))))))))) && ((((s1_lambda == _x_s1_lambda) && (_x_s1_x == 0.0)) && ((( !(_x_s1_l0 != 0)) && ( !(_x_s1_l1 != 0))) || ((_x_s1_l0 != 0) && ( !(_x_s1_l1 != 0))))) || ( !(((s1_l1 != 0) && ( !(s1_l0 != 0))) && ((delta == 0.0) && ( !(( !(s1_evt2 != 0)) && (( !(s1_evt0 != 0)) && ( !(s1_evt1 != 0)))))))))) && (((s1_lambda <= s1_x) && ((( !(s1_evt2 != 0)) && ((s1_evt1 != 0) && ( !(s1_evt0 != 0)))) && (_x_s1_backoff <= s1_backoff))) || ( !((( !(_x_s1_l0 != 0)) && ( !(_x_s1_l1 != 0))) && (((s1_l1 != 0) && ( !(s1_l0 != 0))) && ((delta == 0.0) && ( !(( !(s1_evt2 != 0)) && (( !(s1_evt0 != 0)) && ( !(s1_evt1 != 0))))))))))) && (((( !(s1_evt2 != 0)) && ((s1_evt0 != 0) && ( !(s1_evt1 != 0)))) && ((s1_backoff + (-1.0 * _x_s1_backoff)) <= -1.0)) || ( !(((_x_s1_l0 != 0) && ( !(_x_s1_l1 != 0))) && (((s1_l1 != 0) && ( !(s1_l0 != 0))) && ((delta == 0.0) && ( !(( !(s1_evt2 != 0)) && (( !(s1_evt0 != 0)) && ( !(s1_evt1 != 0))))))))))) && (((s1_lambda == _x_s1_lambda) && ((((_x_s1_l1 != 0) && ( !(_x_s1_l0 != 0))) || ((_x_s1_l0 != 0) && ( !(_x_s1_l1 != 0)))) && ((s1_backoff == _x_s1_backoff) && (_x_s1_x == 0.0)))) || ( !(((s1_l0 != 0) && ( !(s1_l1 != 0))) && ((delta == 0.0) && ( !(( !(s1_evt2 != 0)) && (( !(s1_evt0 != 0)) && ( !(s1_evt1 != 0)))))))))) && ((( !(s1_evt2 != 0)) && ((s1_evt0 != 0) && ( !(s1_evt1 != 0)))) || ( !(((_x_s1_l0 != 0) && ( !(_x_s1_l1 != 0))) && (((s1_l0 != 0) && ( !(s1_l1 != 0))) && ((delta == 0.0) && ( !(( !(s1_evt2 != 0)) && (( !(s1_evt0 != 0)) && ( !(s1_evt1 != 0))))))))))) && ((((s1_evt2 != 0) && (( !(s1_evt0 != 0)) && ( !(s1_evt1 != 0)))) && (s1_backoff <= s1_x)) || ( !(((_x_s1_l1 != 0) && ( !(_x_s1_l0 != 0))) && (((s1_l0 != 0) && ( !(s1_l1 != 0))) && ((delta == 0.0) && ( !(( !(s1_evt2 != 0)) && (( !(s1_evt0 != 0)) && ( !(s1_evt1 != 0))))))))))) && (((((((((((((((((( !(_x_s0_evt2 != 0)) && ((_x_s0_evt0 != 0) && ( !(_x_s0_evt1 != 0)))) || (((( !(_x_s0_evt2 != 0)) && (( !(_x_s0_evt0 != 0)) && ( !(_x_s0_evt1 != 0)))) || ((_x_s0_evt2 != 0) && (( !(_x_s0_evt0 != 0)) && ( !(_x_s0_evt1 != 0))))) || ((( !(_x_s0_evt2 != 0)) && ((_x_s0_evt1 != 0) && ( !(_x_s0_evt0 != 0)))) || ((_x_s0_evt2 != 0) && ((_x_s0_evt1 != 0) && ( !(_x_s0_evt0 != 0))))))) && ((( !(_x_s0_l0 != 0)) && ( !(_x_s0_l1 != 0))) || (((_x_s0_l1 != 0) && ( !(_x_s0_l0 != 0))) || ((_x_s0_l0 != 0) && ( !(_x_s0_l1 != 0)))))) && (13.0 <= _x_s0_backoff)) && (( !(_x_s0_lambda <= 0.0)) && ((_x_s0_x <= _x_s0_lambda) || ( !((_x_s0_l1 != 0) && ( !(_x_s0_l0 != 0))))))) && ((((((s0_l0 != 0) == (_x_s0_l0 != 0)) && ((s0_l1 != 0) == (_x_s0_l1 != 0))) && (s0_lambda == _x_s0_lambda)) && (((delta + (s0_x + (-1.0 * _x_s0_x))) == 0.0) && (s0_backoff == _x_s0_backoff))) || ( !(( !(delta <= 0.0)) || (( !(s0_evt2 != 0)) && (( !(s0_evt0 != 0)) && ( !(s0_evt1 != 0)))))))) && (((((_x_s0_l0 != 0) && ( !(_x_s0_l1 != 0))) || ((( !(_x_s0_l0 != 0)) && ( !(_x_s0_l1 != 0))) || ((_x_s0_l1 != 0) && ( !(_x_s0_l0 != 0))))) && ((s0_backoff == _x_s0_backoff) && (_x_s0_x == 0.0))) || ( !((( !(s0_l0 != 0)) && ( !(s0_l1 != 0))) && ((delta == 0.0) && ( !(( !(s0_evt2 != 0)) && (( !(s0_evt0 != 0)) && ( !(s0_evt1 != 0)))))))))) && (((( !(s0_evt2 != 0)) && ((s0_evt0 != 0) && ( !(s0_evt1 != 0)))) && (s0_lambda == _x_s0_lambda)) || ( !((( !(_x_s0_l0 != 0)) && ( !(_x_s0_l1 != 0))) && ((( !(s0_l0 != 0)) && ( !(s0_l1 != 0))) && ((delta == 0.0) && ( !(( !(s0_evt2 != 0)) && (( !(s0_evt0 != 0)) && ( !(s0_evt1 != 0))))))))))) && (((s0_evt2 != 0) && (( !(s0_evt0 != 0)) && ( !(s0_evt1 != 0)))) || ( !(((_x_s0_l1 != 0) && ( !(_x_s0_l0 != 0))) && ((( !(s0_l0 != 0)) && ( !(s0_l1 != 0))) && ((delta == 0.0) && ( !(( !(s0_evt2 != 0)) && (( !(s0_evt0 != 0)) && ( !(s0_evt1 != 0))))))))))) && (((s0_lambda == _x_s0_lambda) && (((s0_evt2 != 0) && ((s0_evt1 != 0) && ( !(s0_evt0 != 0)))) || (( !(s0_evt2 != 0)) && ((s0_evt0 != 0) && ( !(s0_evt1 != 0)))))) || ( !(((_x_s0_l0 != 0) && ( !(_x_s0_l1 != 0))) && ((( !(s0_l0 != 0)) && ( !(s0_l1 != 0))) && ((delta == 0.0) && ( !(( !(s0_evt2 != 0)) && (( !(s0_evt0 != 0)) && ( !(s0_evt1 != 0))))))))))) && ((((s0_lambda == _x_s0_lambda) && (_x_s0_x == 0.0)) && ((( !(_x_s0_l0 != 0)) && ( !(_x_s0_l1 != 0))) || ((_x_s0_l0 != 0) && ( !(_x_s0_l1 != 0))))) || ( !(((s0_l1 != 0) && ( !(s0_l0 != 0))) && ((delta == 0.0) && ( !(( !(s0_evt2 != 0)) && (( !(s0_evt0 != 0)) && ( !(s0_evt1 != 0)))))))))) && (((s0_lambda <= s0_x) && ((( !(s0_evt2 != 0)) && ((s0_evt1 != 0) && ( !(s0_evt0 != 0)))) && (_x_s0_backoff <= s0_backoff))) || ( !((( !(_x_s0_l0 != 0)) && ( !(_x_s0_l1 != 0))) && (((s0_l1 != 0) && ( !(s0_l0 != 0))) && ((delta == 0.0) && ( !(( !(s0_evt2 != 0)) && (( !(s0_evt0 != 0)) && ( !(s0_evt1 != 0))))))))))) && (((( !(s0_evt2 != 0)) && ((s0_evt0 != 0) && ( !(s0_evt1 != 0)))) && ((s0_backoff + (-1.0 * _x_s0_backoff)) <= -1.0)) || ( !(((_x_s0_l0 != 0) && ( !(_x_s0_l1 != 0))) && (((s0_l1 != 0) && ( !(s0_l0 != 0))) && ((delta == 0.0) && ( !(( !(s0_evt2 != 0)) && (( !(s0_evt0 != 0)) && ( !(s0_evt1 != 0))))))))))) && (((s0_lambda == _x_s0_lambda) && ((((_x_s0_l1 != 0) && ( !(_x_s0_l0 != 0))) || ((_x_s0_l0 != 0) && ( !(_x_s0_l1 != 0)))) && ((s0_backoff == _x_s0_backoff) && (_x_s0_x == 0.0)))) || ( !(((s0_l0 != 0) && ( !(s0_l1 != 0))) && ((delta == 0.0) && ( !(( !(s0_evt2 != 0)) && (( !(s0_evt0 != 0)) && ( !(s0_evt1 != 0)))))))))) && ((( !(s0_evt2 != 0)) && ((s0_evt0 != 0) && ( !(s0_evt1 != 0)))) || ( !(((_x_s0_l0 != 0) && ( !(_x_s0_l1 != 0))) && (((s0_l0 != 0) && ( !(s0_l1 != 0))) && ((delta == 0.0) && ( !(( !(s0_evt2 != 0)) && (( !(s0_evt0 != 0)) && ( !(s0_evt1 != 0))))))))))) && ((((s0_evt2 != 0) && (( !(s0_evt0 != 0)) && ( !(s0_evt1 != 0)))) && (s0_backoff <= s0_x)) || ( !(((_x_s0_l1 != 0) && ( !(_x_s0_l0 != 0))) && (((s0_l0 != 0) && ( !(s0_l1 != 0))) && ((delta == 0.0) && ( !(( !(s0_evt2 != 0)) && (( !(s0_evt0 != 0)) && ( !(s0_evt1 != 0))))))))))) && (((((((((((((((( !(_x_bus_evt2 != 0)) && (( !(_x_bus_evt0 != 0)) && ( !(_x_bus_evt1 != 0)))) || ((((_x_bus_evt2 != 0) && (( !(_x_bus_evt0 != 0)) && ( !(_x_bus_evt1 != 0)))) || (( !(_x_bus_evt2 != 0)) && ((_x_bus_evt1 != 0) && ( !(_x_bus_evt0 != 0))))) || (((_x_bus_evt2 != 0) && ((_x_bus_evt1 != 0) && ( !(_x_bus_evt0 != 0)))) || (( !(_x_bus_evt2 != 0)) && ((_x_bus_evt0 != 0) && ( !(_x_bus_evt1 != 0))))))) && (((( !(_x_bus_l0 != 0)) && ( !(_x_bus_l1 != 0))) || ((_x_bus_l1 != 0) && ( !(_x_bus_l0 != 0)))) || (((_x_bus_l0 != 0) && ( !(_x_bus_l1 != 0))) || ((_x_bus_l0 != 0) && (_x_bus_l1 != 0))))) && ((( !(13.0 <= _x_bus_x)) || ( !((_x_bus_l0 != 0) && ( !(_x_bus_l1 != 0))))) && ((_x_delta == 0.0) || ( !((_x_bus_l0 != 0) && (_x_bus_l1 != 0)))))) && ((delta <= 0.0) || (((delta + (bus_x + (-1.0 * _x_bus_x))) == 0.0) && ((((bus_l0 != 0) == (_x_bus_l0 != 0)) && ((bus_l1 != 0) == (_x_bus_l1 != 0))) && (bus_j == _x_bus_j))))) && ((((delta + (bus_x + (-1.0 * _x_bus_x))) == 0.0) && ((((bus_l0 != 0) == (_x_bus_l0 != 0)) && ((bus_l1 != 0) == (_x_bus_l1 != 0))) && (bus_j == _x_bus_j))) || ( !(( !(bus_evt2 != 0)) && (( !(bus_evt0 != 0)) && ( !(bus_evt1 != 0))))))) && (((((bus_evt2 != 0) && (( !(bus_evt0 != 0)) && ( !(bus_evt1 != 0)))) && ((_x_bus_l1 != 0) && ( !(_x_bus_l0 != 0)))) && ((bus_j == _x_bus_j) && (_x_bus_x == 0.0))) || ( !((( !(bus_l0 != 0)) && ( !(bus_l1 != 0))) && ((delta == 0.0) && ( !(( !(bus_evt2 != 0)) && (( !(bus_evt0 != 0)) && ( !(bus_evt1 != 0)))))))))) && (((bus_j == _x_bus_j) && (((_x_bus_l0 != 0) && ( !(_x_bus_l1 != 0))) || ((( !(_x_bus_l0 != 0)) && ( !(_x_bus_l1 != 0))) || ((_x_bus_l1 != 0) && ( !(_x_bus_l0 != 0)))))) || ( !(((bus_l1 != 0) && ( !(bus_l0 != 0))) && ((delta == 0.0) && ( !(( !(bus_evt2 != 0)) && (( !(bus_evt0 != 0)) && ( !(bus_evt1 != 0)))))))))) && (((( !(bus_evt2 != 0)) && ((bus_evt1 != 0) && ( !(bus_evt0 != 0)))) && (_x_bus_x == 0.0)) || ( !(((delta == 0.0) && ( !(( !(bus_evt2 != 0)) && (( !(bus_evt0 != 0)) && ( !(bus_evt1 != 0)))))) && ((( !(_x_bus_l0 != 0)) && ( !(_x_bus_l1 != 0))) && ((bus_l1 != 0) && ( !(bus_l0 != 0)))))))) && ((((bus_evt2 != 0) && ((bus_evt1 != 0) && ( !(bus_evt0 != 0)))) && ((13.0 <= bus_x) && (bus_x == _x_bus_x))) || ( !(((delta == 0.0) && ( !(( !(bus_evt2 != 0)) && (( !(bus_evt0 != 0)) && ( !(bus_evt1 != 0)))))) && (((bus_l1 != 0) && ( !(bus_l0 != 0))) && ((_x_bus_l1 != 0) && ( !(_x_bus_l0 != 0)))))))) && ((((bus_evt2 != 0) && (( !(bus_evt0 != 0)) && ( !(bus_evt1 != 0)))) && (( !(13.0 <= bus_x)) && (_x_bus_x == 0.0))) || ( !(((delta == 0.0) && ( !(( !(bus_evt2 != 0)) && (( !(bus_evt0 != 0)) && ( !(bus_evt1 != 0)))))) && (((bus_l1 != 0) && ( !(bus_l0 != 0))) && ((_x_bus_l0 != 0) && ( !(_x_bus_l1 != 0)))))))) && ((((((_x_bus_l0 != 0) && (_x_bus_l1 != 0)) && ( !(13.0 <= bus_x))) && ((( !(bus_evt2 != 0)) && ((bus_evt0 != 0) && ( !(bus_evt1 != 0)))) && (bus_cd_id == bus_j))) && ((_x_bus_x == 0.0) && ((bus_j + (-1 * _x_bus_j)) == -1))) || ( !(((bus_l0 != 0) && ( !(bus_l1 != 0))) && ((delta == 0.0) && ( !(( !(bus_evt2 != 0)) && (( !(bus_evt0 != 0)) && ( !(bus_evt1 != 0)))))))))) && ((((bus_j + (-1 * _x_bus_j)) == -1) && (((( !(bus_evt2 != 0)) && ((bus_evt0 != 0) && ( !(bus_evt1 != 0)))) && (bus_cd_id == bus_j)) && ((_x_bus_x == 0.0) && ( !(2 <= bus_j))))) || ( !(((delta == 0.0) && ( !(( !(bus_evt2 != 0)) && (( !(bus_evt0 != 0)) && ( !(bus_evt1 != 0)))))) && (((bus_l0 != 0) && (bus_l1 != 0)) && ((_x_bus_l0 != 0) && (_x_bus_l1 != 0))))))) && (((((( !(bus_evt2 != 0)) && ((bus_evt0 != 0) && ( !(bus_evt1 != 0)))) && (bus_j == 2)) && ((_x_bus_x == 0.0) && (bus_cd_id == bus_j))) && (_x_bus_j == 0)) || ( !(((delta == 0.0) && ( !(( !(bus_evt2 != 0)) && (( !(bus_evt0 != 0)) && ( !(bus_evt1 != 0)))))) && ((( !(_x_bus_l0 != 0)) && ( !(_x_bus_l1 != 0))) && ((bus_l0 != 0) && (bus_l1 != 0))))))) && (0.0 <= _x_delta))))) && (((((( !(s0_evt2 != 0)) && (( !(s0_evt0 != 0)) && ( !(s0_evt1 != 0)))) || (( !(s1_evt2 != 0)) && (( !(s1_evt0 != 0)) && ( !(s1_evt1 != 0))))) && ((( !(s0_evt2 != 0)) && (( !(s0_evt0 != 0)) && ( !(s0_evt1 != 0)))) || (( !(s2_evt2 != 0)) && (( !(s2_evt0 != 0)) && ( !(s2_evt1 != 0)))))) && ((( !(s1_evt2 != 0)) && (( !(s1_evt0 != 0)) && ( !(s1_evt1 != 0)))) || (( !(s2_evt2 != 0)) && (( !(s2_evt0 != 0)) && ( !(s2_evt1 != 0)))))) || ( !(delta == 0.0)))) && (( !(delta == 0.0)) || (( !(( !(s2_evt2 != 0)) && (( !(s2_evt0 != 0)) && ( !(s2_evt1 != 0))))) || (( !(( !(s1_evt2 != 0)) && (( !(s1_evt0 != 0)) && ( !(s1_evt1 != 0))))) || (( !(( !(bus_evt2 != 0)) && (( !(bus_evt0 != 0)) && ( !(bus_evt1 != 0))))) || ( !(( !(s0_evt2 != 0)) && (( !(s0_evt0 != 0)) && ( !(s0_evt1 != 0)))))))))) && (( !(delta == 0.0)) || (((((bus_evt2 != 0) && (( !(bus_evt0 != 0)) && ( !(bus_evt1 != 0)))) == (((s2_evt2 != 0) && (( !(s2_evt0 != 0)) && ( !(s2_evt1 != 0)))) || (((s0_evt2 != 0) && (( !(s0_evt0 != 0)) && ( !(s0_evt1 != 0)))) || ((s1_evt2 != 0) && (( !(s1_evt0 != 0)) && ( !(s1_evt1 != 0))))))) && ((( !(bus_evt2 != 0)) && ((bus_evt1 != 0) && ( !(bus_evt0 != 0)))) == ((( !(s2_evt2 != 0)) && ((s2_evt1 != 0) && ( !(s2_evt0 != 0)))) || ((( !(s0_evt2 != 0)) && ((s0_evt1 != 0) && ( !(s0_evt0 != 0)))) || (( !(s1_evt2 != 0)) && ((s1_evt1 != 0) && ( !(s1_evt0 != 0)))))))) && ((((bus_evt2 != 0) && ((bus_evt1 != 0) && ( !(bus_evt0 != 0)))) == (((s2_evt2 != 0) && ((s2_evt1 != 0) && ( !(s2_evt0 != 0)))) || (((s0_evt2 != 0) && ((s0_evt1 != 0) && ( !(s0_evt0 != 0)))) || ((s1_evt2 != 0) && ((s1_evt1 != 0) && ( !(s1_evt0 != 0))))))) && ((( !(bus_evt2 != 0)) && ((bus_evt0 != 0) && ( !(bus_evt1 != 0)))) == ((( !(s2_evt2 != 0)) && ((s2_evt0 != 0) && ( !(s2_evt1 != 0)))) || ((( !(s0_evt2 != 0)) && ((s0_evt0 != 0) && ( !(s0_evt1 != 0)))) || (( !(s1_evt2 != 0)) && ((s1_evt0 != 0) && ( !(s1_evt1 != 0))))))))))) && (( !(delta == 0.0)) || ((((( !(s0_evt2 != 0)) && ((s0_evt0 != 0) && ( !(s0_evt1 != 0)))) == ((( !(bus_evt2 != 0)) && ((bus_evt0 != 0) && ( !(bus_evt1 != 0)))) && (bus_cd_id == 0))) && ((( !(s1_evt2 != 0)) && ((s1_evt0 != 0) && ( !(s1_evt1 != 0)))) == ((( !(bus_evt2 != 0)) && ((bus_evt0 != 0) && ( !(bus_evt1 != 0)))) && (bus_cd_id == 1)))) && ((( !(s2_evt2 != 0)) && ((s2_evt0 != 0) && ( !(s2_evt1 != 0)))) == ((( !(bus_evt2 != 0)) && ((bus_evt0 != 0) && ( !(bus_evt1 != 0)))) && (bus_cd_id == 2)))))) && (((delta == _x__diverge_delta) || ( !(1.0 <= _diverge_delta))) && ((1.0 <= _diverge_delta) || ((delta + (_diverge_delta + (-1.0 * _x__diverge_delta))) == 0.0))));
    _diverge_delta = _x__diverge_delta;
    s2_l1 = _x_s2_l1;
    s2_l0 = _x_s2_l0;
    s2_evt2 = _x_s2_evt2;
    s0_evt0 = _x_s0_evt0;
    bus_l1 = _x_bus_l1;
    bus_evt2 = _x_bus_evt2;
    s0_backoff = _x_s0_backoff;
    s0_lambda = _x_s0_lambda;
    s1_evt0 = _x_s1_evt0;
    delta = _x_delta;
    s2_evt1 = _x_s2_evt1;
    bus_x = _x_bus_x;
    s1_lambda = _x_s1_lambda;
    s0_x = _x_s0_x;
    s2_evt0 = _x_s2_evt0;
    bus_j = _x_bus_j;
    s1_x = _x_s1_x;
    s0_evt1 = _x_s0_evt1;
    s0_evt2 = _x_s0_evt2;
    s0_l0 = _x_s0_l0;
    s2_lambda = _x_s2_lambda;
    s0_l1 = _x_s0_l1;
    s2_backoff = _x_s2_backoff;
    bus_cd_id = _x_bus_cd_id;
    s1_backoff = _x_s1_backoff;
    bus_evt0 = _x_bus_evt0;
    s1_evt1 = _x_s1_evt1;
    bus_evt1 = _x_bus_evt1;
    s1_evt2 = _x_s1_evt2;
    s1_l0 = _x_s1_l0;
    bus_l0 = _x_bus_l0;
    s1_l1 = _x_s1_l1;
    s2_x = _x_s2_x;

  }
}
