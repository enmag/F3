//@ ltl invariant negative: ( ( ([] (<> ( (! AP((s0_l0 != 0))) && (! AP((s0_l1 != 0)))))) || (! ([] (<> ( AP((s0_l1 != 0)) && (! AP((s0_l0 != 0)))))))) || (! ([] (<> AP((1.0 <= _diverge_delta))))));

extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);

char __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}


char s1_l1, _x_s1_l1;
char s1_l0, _x_s1_l0;
char s1_evt2, _x_s1_evt2;
char s1_evt1, _x_s1_evt1;
float s1_backoff, _x_s1_backoff;
char s0_l1, _x_s0_l1;
float _diverge_delta, _x__diverge_delta;
char s0_l0, _x_s0_l0;
char s0_evt2, _x_s0_evt2;
char s0_evt1, _x_s0_evt1;
float s1_x, _x_s1_x;
int bus_j, _x_bus_j;
float s0_x, _x_s0_x;
float s1_lambda, _x_s1_lambda;
float bus_x, _x_bus_x;
float delta, _x_delta;
float s0_lambda, _x_s0_lambda;
int bus_cd_id, _x_bus_cd_id;
float s0_backoff, _x_s0_backoff;
char bus_evt0, _x_bus_evt0;
char bus_evt1, _x_bus_evt1;
char bus_l0, _x_bus_l0;
char s1_evt0, _x_s1_evt0;
char bus_evt2, _x_bus_evt2;
char bus_l1, _x_bus_l1;
char s0_evt0, _x_s0_evt0;

int main()
{
  s1_l1 = __VERIFIER_nondet_bool();
  s1_l0 = __VERIFIER_nondet_bool();
  s1_evt2 = __VERIFIER_nondet_bool();
  s1_evt1 = __VERIFIER_nondet_bool();
  s1_backoff = __VERIFIER_nondet_float();
  s0_l1 = __VERIFIER_nondet_bool();
  _diverge_delta = __VERIFIER_nondet_float();
  s0_l0 = __VERIFIER_nondet_bool();
  s0_evt2 = __VERIFIER_nondet_bool();
  s0_evt1 = __VERIFIER_nondet_bool();
  s1_x = __VERIFIER_nondet_float();
  bus_j = __VERIFIER_nondet_int();
  s0_x = __VERIFIER_nondet_float();
  s1_lambda = __VERIFIER_nondet_float();
  bus_x = __VERIFIER_nondet_float();
  delta = __VERIFIER_nondet_float();
  s0_lambda = __VERIFIER_nondet_float();
  bus_cd_id = __VERIFIER_nondet_int();
  s0_backoff = __VERIFIER_nondet_float();
  bus_evt0 = __VERIFIER_nondet_bool();
  bus_evt1 = __VERIFIER_nondet_bool();
  bus_l0 = __VERIFIER_nondet_bool();
  s1_evt0 = __VERIFIER_nondet_bool();
  bus_evt2 = __VERIFIER_nondet_bool();
  bus_l1 = __VERIFIER_nondet_bool();
  s0_evt0 = __VERIFIER_nondet_bool();

  int __ok = ((((((((( !(s1_l0 != 0)) && ( !(s1_l1 != 0))) && (s1_x == 0.0)) && ((( !(s1_evt2 != 0)) && ((s1_evt0 != 0) && ( !(s1_evt1 != 0)))) || (((( !(s1_evt2 != 0)) && (( !(s1_evt0 != 0)) && ( !(s1_evt1 != 0)))) || ((s1_evt2 != 0) && (( !(s1_evt0 != 0)) && ( !(s1_evt1 != 0))))) || ((( !(s1_evt2 != 0)) && ((s1_evt1 != 0) && ( !(s1_evt0 != 0)))) || ((s1_evt2 != 0) && ((s1_evt1 != 0) && ( !(s1_evt0 != 0)))))))) && ((( !(s1_l0 != 0)) && ( !(s1_l1 != 0))) || (((s1_l1 != 0) && ( !(s1_l0 != 0))) || ((s1_l0 != 0) && ( !(s1_l1 != 0)))))) && (13.0 <= s1_backoff)) && (( !(s1_lambda <= 0.0)) && ((s1_x <= s1_lambda) || ( !((s1_l1 != 0) && ( !(s1_l0 != 0))))))) && (((((((( !(s0_l0 != 0)) && ( !(s0_l1 != 0))) && (s0_x == 0.0)) && ((( !(s0_evt2 != 0)) && ((s0_evt0 != 0) && ( !(s0_evt1 != 0)))) || (((( !(s0_evt2 != 0)) && (( !(s0_evt0 != 0)) && ( !(s0_evt1 != 0)))) || ((s0_evt2 != 0) && (( !(s0_evt0 != 0)) && ( !(s0_evt1 != 0))))) || ((( !(s0_evt2 != 0)) && ((s0_evt1 != 0) && ( !(s0_evt0 != 0)))) || ((s0_evt2 != 0) && ((s0_evt1 != 0) && ( !(s0_evt0 != 0)))))))) && ((( !(s0_l0 != 0)) && ( !(s0_l1 != 0))) || (((s0_l1 != 0) && ( !(s0_l0 != 0))) || ((s0_l0 != 0) && ( !(s0_l1 != 0)))))) && (13.0 <= s0_backoff)) && (( !(s0_lambda <= 0.0)) && ((s0_x <= s0_lambda) || ( !((s0_l1 != 0) && ( !(s0_l0 != 0))))))) && (((((( !(bus_l0 != 0)) && ( !(bus_l1 != 0))) && (((( !(bus_evt2 != 0)) && (( !(bus_evt0 != 0)) && ( !(bus_evt1 != 0)))) || ((((bus_evt2 != 0) && (( !(bus_evt0 != 0)) && ( !(bus_evt1 != 0)))) || (( !(bus_evt2 != 0)) && ((bus_evt1 != 0) && ( !(bus_evt0 != 0))))) || (((bus_evt2 != 0) && ((bus_evt1 != 0) && ( !(bus_evt0 != 0)))) || (( !(bus_evt2 != 0)) && ((bus_evt0 != 0) && ( !(bus_evt1 != 0))))))) && (((( !(bus_l0 != 0)) && ( !(bus_l1 != 0))) || ((bus_l1 != 0) && ( !(bus_l0 != 0)))) || (((bus_l0 != 0) && ( !(bus_l1 != 0))) || ((bus_l0 != 0) && (bus_l1 != 0)))))) && ((bus_j == 0) && (bus_x == 0.0))) && ((( !(13.0 <= bus_x)) || ( !((bus_l0 != 0) && ( !(bus_l1 != 0))))) && ((delta == 0.0) || ( !((bus_l0 != 0) && (bus_l1 != 0)))))) && (0.0 <= delta)))) && (delta == _diverge_delta));
  while (__ok) {
    _x_s1_l1 = __VERIFIER_nondet_bool();
    _x_s1_l0 = __VERIFIER_nondet_bool();
    _x_s1_evt2 = __VERIFIER_nondet_bool();
    _x_s1_evt1 = __VERIFIER_nondet_bool();
    _x_s1_backoff = __VERIFIER_nondet_float();
    _x_s0_l1 = __VERIFIER_nondet_bool();
    _x__diverge_delta = __VERIFIER_nondet_float();
    _x_s0_l0 = __VERIFIER_nondet_bool();
    _x_s0_evt2 = __VERIFIER_nondet_bool();
    _x_s0_evt1 = __VERIFIER_nondet_bool();
    _x_s1_x = __VERIFIER_nondet_float();
    _x_bus_j = __VERIFIER_nondet_int();
    _x_s0_x = __VERIFIER_nondet_float();
    _x_s1_lambda = __VERIFIER_nondet_float();
    _x_bus_x = __VERIFIER_nondet_float();
    _x_delta = __VERIFIER_nondet_float();
    _x_s0_lambda = __VERIFIER_nondet_float();
    _x_bus_cd_id = __VERIFIER_nondet_int();
    _x_s0_backoff = __VERIFIER_nondet_float();
    _x_bus_evt0 = __VERIFIER_nondet_bool();
    _x_bus_evt1 = __VERIFIER_nondet_bool();
    _x_bus_l0 = __VERIFIER_nondet_bool();
    _x_s1_evt0 = __VERIFIER_nondet_bool();
    _x_bus_evt2 = __VERIFIER_nondet_bool();
    _x_bus_l1 = __VERIFIER_nondet_bool();
    _x_s0_evt0 = __VERIFIER_nondet_bool();

    __ok = ((((((((((((((((((((((( !(_x_s1_evt2 != 0)) && ((_x_s1_evt0 != 0) && ( !(_x_s1_evt1 != 0)))) || (((( !(_x_s1_evt2 != 0)) && (( !(_x_s1_evt0 != 0)) && ( !(_x_s1_evt1 != 0)))) || ((_x_s1_evt2 != 0) && (( !(_x_s1_evt0 != 0)) && ( !(_x_s1_evt1 != 0))))) || ((( !(_x_s1_evt2 != 0)) && ((_x_s1_evt1 != 0) && ( !(_x_s1_evt0 != 0)))) || ((_x_s1_evt2 != 0) && ((_x_s1_evt1 != 0) && ( !(_x_s1_evt0 != 0))))))) && ((( !(_x_s1_l0 != 0)) && ( !(_x_s1_l1 != 0))) || (((_x_s1_l1 != 0) && ( !(_x_s1_l0 != 0))) || ((_x_s1_l0 != 0) && ( !(_x_s1_l1 != 0)))))) && (13.0 <= _x_s1_backoff)) && (( !(_x_s1_lambda <= 0.0)) && ((_x_s1_x <= _x_s1_lambda) || ( !((_x_s1_l1 != 0) && ( !(_x_s1_l0 != 0))))))) && ((((((s1_l0 != 0) == (_x_s1_l0 != 0)) && ((s1_l1 != 0) == (_x_s1_l1 != 0))) && (s1_lambda == _x_s1_lambda)) && (((delta + (s1_x + (-1.0 * _x_s1_x))) == 0.0) && (s1_backoff == _x_s1_backoff))) || ( !(( !(delta <= 0.0)) || (( !(s1_evt2 != 0)) && (( !(s1_evt0 != 0)) && ( !(s1_evt1 != 0)))))))) && (((((_x_s1_l0 != 0) && ( !(_x_s1_l1 != 0))) || ((( !(_x_s1_l0 != 0)) && ( !(_x_s1_l1 != 0))) || ((_x_s1_l1 != 0) && ( !(_x_s1_l0 != 0))))) && ((s1_backoff == _x_s1_backoff) && (_x_s1_x == 0.0))) || ( !((( !(s1_l0 != 0)) && ( !(s1_l1 != 0))) && ((delta == 0.0) && ( !(( !(s1_evt2 != 0)) && (( !(s1_evt0 != 0)) && ( !(s1_evt1 != 0)))))))))) && (((( !(s1_evt2 != 0)) && ((s1_evt0 != 0) && ( !(s1_evt1 != 0)))) && (s1_lambda == _x_s1_lambda)) || ( !((( !(_x_s1_l0 != 0)) && ( !(_x_s1_l1 != 0))) && ((( !(s1_l0 != 0)) && ( !(s1_l1 != 0))) && ((delta == 0.0) && ( !(( !(s1_evt2 != 0)) && (( !(s1_evt0 != 0)) && ( !(s1_evt1 != 0))))))))))) && (((s1_evt2 != 0) && (( !(s1_evt0 != 0)) && ( !(s1_evt1 != 0)))) || ( !(((_x_s1_l1 != 0) && ( !(_x_s1_l0 != 0))) && ((( !(s1_l0 != 0)) && ( !(s1_l1 != 0))) && ((delta == 0.0) && ( !(( !(s1_evt2 != 0)) && (( !(s1_evt0 != 0)) && ( !(s1_evt1 != 0))))))))))) && (((s1_lambda == _x_s1_lambda) && (((s1_evt2 != 0) && ((s1_evt1 != 0) && ( !(s1_evt0 != 0)))) || (( !(s1_evt2 != 0)) && ((s1_evt0 != 0) && ( !(s1_evt1 != 0)))))) || ( !(((_x_s1_l0 != 0) && ( !(_x_s1_l1 != 0))) && ((( !(s1_l0 != 0)) && ( !(s1_l1 != 0))) && ((delta == 0.0) && ( !(( !(s1_evt2 != 0)) && (( !(s1_evt0 != 0)) && ( !(s1_evt1 != 0))))))))))) && ((((s1_lambda == _x_s1_lambda) && (_x_s1_x == 0.0)) && ((( !(_x_s1_l0 != 0)) && ( !(_x_s1_l1 != 0))) || ((_x_s1_l0 != 0) && ( !(_x_s1_l1 != 0))))) || ( !(((s1_l1 != 0) && ( !(s1_l0 != 0))) && ((delta == 0.0) && ( !(( !(s1_evt2 != 0)) && (( !(s1_evt0 != 0)) && ( !(s1_evt1 != 0)))))))))) && (((s1_lambda <= s1_x) && ((( !(s1_evt2 != 0)) && ((s1_evt1 != 0) && ( !(s1_evt0 != 0)))) && (_x_s1_backoff <= s1_backoff))) || ( !((( !(_x_s1_l0 != 0)) && ( !(_x_s1_l1 != 0))) && (((s1_l1 != 0) && ( !(s1_l0 != 0))) && ((delta == 0.0) && ( !(( !(s1_evt2 != 0)) && (( !(s1_evt0 != 0)) && ( !(s1_evt1 != 0))))))))))) && (((( !(s1_evt2 != 0)) && ((s1_evt0 != 0) && ( !(s1_evt1 != 0)))) && ((s1_backoff + (-1.0 * _x_s1_backoff)) <= -1.0)) || ( !(((_x_s1_l0 != 0) && ( !(_x_s1_l1 != 0))) && (((s1_l1 != 0) && ( !(s1_l0 != 0))) && ((delta == 0.0) && ( !(( !(s1_evt2 != 0)) && (( !(s1_evt0 != 0)) && ( !(s1_evt1 != 0))))))))))) && (((s1_lambda == _x_s1_lambda) && ((((_x_s1_l1 != 0) && ( !(_x_s1_l0 != 0))) || ((_x_s1_l0 != 0) && ( !(_x_s1_l1 != 0)))) && ((s1_backoff == _x_s1_backoff) && (_x_s1_x == 0.0)))) || ( !(((s1_l0 != 0) && ( !(s1_l1 != 0))) && ((delta == 0.0) && ( !(( !(s1_evt2 != 0)) && (( !(s1_evt0 != 0)) && ( !(s1_evt1 != 0)))))))))) && ((( !(s1_evt2 != 0)) && ((s1_evt0 != 0) && ( !(s1_evt1 != 0)))) || ( !(((_x_s1_l0 != 0) && ( !(_x_s1_l1 != 0))) && (((s1_l0 != 0) && ( !(s1_l1 != 0))) && ((delta == 0.0) && ( !(( !(s1_evt2 != 0)) && (( !(s1_evt0 != 0)) && ( !(s1_evt1 != 0))))))))))) && ((((s1_evt2 != 0) && (( !(s1_evt0 != 0)) && ( !(s1_evt1 != 0)))) && (s1_backoff <= s1_x)) || ( !(((_x_s1_l1 != 0) && ( !(_x_s1_l0 != 0))) && (((s1_l0 != 0) && ( !(s1_l1 != 0))) && ((delta == 0.0) && ( !(( !(s1_evt2 != 0)) && (( !(s1_evt0 != 0)) && ( !(s1_evt1 != 0))))))))))) && (((((((((((((((((( !(_x_s0_evt2 != 0)) && ((_x_s0_evt0 != 0) && ( !(_x_s0_evt1 != 0)))) || (((( !(_x_s0_evt2 != 0)) && (( !(_x_s0_evt0 != 0)) && ( !(_x_s0_evt1 != 0)))) || ((_x_s0_evt2 != 0) && (( !(_x_s0_evt0 != 0)) && ( !(_x_s0_evt1 != 0))))) || ((( !(_x_s0_evt2 != 0)) && ((_x_s0_evt1 != 0) && ( !(_x_s0_evt0 != 0)))) || ((_x_s0_evt2 != 0) && ((_x_s0_evt1 != 0) && ( !(_x_s0_evt0 != 0))))))) && ((( !(_x_s0_l0 != 0)) && ( !(_x_s0_l1 != 0))) || (((_x_s0_l1 != 0) && ( !(_x_s0_l0 != 0))) || ((_x_s0_l0 != 0) && ( !(_x_s0_l1 != 0)))))) && (13.0 <= _x_s0_backoff)) && (( !(_x_s0_lambda <= 0.0)) && ((_x_s0_x <= _x_s0_lambda) || ( !((_x_s0_l1 != 0) && ( !(_x_s0_l0 != 0))))))) && ((((((s0_l0 != 0) == (_x_s0_l0 != 0)) && ((s0_l1 != 0) == (_x_s0_l1 != 0))) && (s0_lambda == _x_s0_lambda)) && (((delta + (s0_x + (-1.0 * _x_s0_x))) == 0.0) && (s0_backoff == _x_s0_backoff))) || ( !(( !(delta <= 0.0)) || (( !(s0_evt2 != 0)) && (( !(s0_evt0 != 0)) && ( !(s0_evt1 != 0)))))))) && (((((_x_s0_l0 != 0) && ( !(_x_s0_l1 != 0))) || ((( !(_x_s0_l0 != 0)) && ( !(_x_s0_l1 != 0))) || ((_x_s0_l1 != 0) && ( !(_x_s0_l0 != 0))))) && ((s0_backoff == _x_s0_backoff) && (_x_s0_x == 0.0))) || ( !((( !(s0_l0 != 0)) && ( !(s0_l1 != 0))) && ((delta == 0.0) && ( !(( !(s0_evt2 != 0)) && (( !(s0_evt0 != 0)) && ( !(s0_evt1 != 0)))))))))) && (((( !(s0_evt2 != 0)) && ((s0_evt0 != 0) && ( !(s0_evt1 != 0)))) && (s0_lambda == _x_s0_lambda)) || ( !((( !(_x_s0_l0 != 0)) && ( !(_x_s0_l1 != 0))) && ((( !(s0_l0 != 0)) && ( !(s0_l1 != 0))) && ((delta == 0.0) && ( !(( !(s0_evt2 != 0)) && (( !(s0_evt0 != 0)) && ( !(s0_evt1 != 0))))))))))) && (((s0_evt2 != 0) && (( !(s0_evt0 != 0)) && ( !(s0_evt1 != 0)))) || ( !(((_x_s0_l1 != 0) && ( !(_x_s0_l0 != 0))) && ((( !(s0_l0 != 0)) && ( !(s0_l1 != 0))) && ((delta == 0.0) && ( !(( !(s0_evt2 != 0)) && (( !(s0_evt0 != 0)) && ( !(s0_evt1 != 0))))))))))) && (((s0_lambda == _x_s0_lambda) && (((s0_evt2 != 0) && ((s0_evt1 != 0) && ( !(s0_evt0 != 0)))) || (( !(s0_evt2 != 0)) && ((s0_evt0 != 0) && ( !(s0_evt1 != 0)))))) || ( !(((_x_s0_l0 != 0) && ( !(_x_s0_l1 != 0))) && ((( !(s0_l0 != 0)) && ( !(s0_l1 != 0))) && ((delta == 0.0) && ( !(( !(s0_evt2 != 0)) && (( !(s0_evt0 != 0)) && ( !(s0_evt1 != 0))))))))))) && ((((s0_lambda == _x_s0_lambda) && (_x_s0_x == 0.0)) && ((( !(_x_s0_l0 != 0)) && ( !(_x_s0_l1 != 0))) || ((_x_s0_l0 != 0) && ( !(_x_s0_l1 != 0))))) || ( !(((s0_l1 != 0) && ( !(s0_l0 != 0))) && ((delta == 0.0) && ( !(( !(s0_evt2 != 0)) && (( !(s0_evt0 != 0)) && ( !(s0_evt1 != 0)))))))))) && (((s0_lambda <= s0_x) && ((( !(s0_evt2 != 0)) && ((s0_evt1 != 0) && ( !(s0_evt0 != 0)))) && (_x_s0_backoff <= s0_backoff))) || ( !((( !(_x_s0_l0 != 0)) && ( !(_x_s0_l1 != 0))) && (((s0_l1 != 0) && ( !(s0_l0 != 0))) && ((delta == 0.0) && ( !(( !(s0_evt2 != 0)) && (( !(s0_evt0 != 0)) && ( !(s0_evt1 != 0))))))))))) && (((( !(s0_evt2 != 0)) && ((s0_evt0 != 0) && ( !(s0_evt1 != 0)))) && ((s0_backoff + (-1.0 * _x_s0_backoff)) <= -1.0)) || ( !(((_x_s0_l0 != 0) && ( !(_x_s0_l1 != 0))) && (((s0_l1 != 0) && ( !(s0_l0 != 0))) && ((delta == 0.0) && ( !(( !(s0_evt2 != 0)) && (( !(s0_evt0 != 0)) && ( !(s0_evt1 != 0))))))))))) && (((s0_lambda == _x_s0_lambda) && ((((_x_s0_l1 != 0) && ( !(_x_s0_l0 != 0))) || ((_x_s0_l0 != 0) && ( !(_x_s0_l1 != 0)))) && ((s0_backoff == _x_s0_backoff) && (_x_s0_x == 0.0)))) || ( !(((s0_l0 != 0) && ( !(s0_l1 != 0))) && ((delta == 0.0) && ( !(( !(s0_evt2 != 0)) && (( !(s0_evt0 != 0)) && ( !(s0_evt1 != 0)))))))))) && ((( !(s0_evt2 != 0)) && ((s0_evt0 != 0) && ( !(s0_evt1 != 0)))) || ( !(((_x_s0_l0 != 0) && ( !(_x_s0_l1 != 0))) && (((s0_l0 != 0) && ( !(s0_l1 != 0))) && ((delta == 0.0) && ( !(( !(s0_evt2 != 0)) && (( !(s0_evt0 != 0)) && ( !(s0_evt1 != 0))))))))))) && ((((s0_evt2 != 0) && (( !(s0_evt0 != 0)) && ( !(s0_evt1 != 0)))) && (s0_backoff <= s0_x)) || ( !(((_x_s0_l1 != 0) && ( !(_x_s0_l0 != 0))) && (((s0_l0 != 0) && ( !(s0_l1 != 0))) && ((delta == 0.0) && ( !(( !(s0_evt2 != 0)) && (( !(s0_evt0 != 0)) && ( !(s0_evt1 != 0))))))))))) && (((((((((((((((( !(_x_bus_evt2 != 0)) && (( !(_x_bus_evt0 != 0)) && ( !(_x_bus_evt1 != 0)))) || ((((_x_bus_evt2 != 0) && (( !(_x_bus_evt0 != 0)) && ( !(_x_bus_evt1 != 0)))) || (( !(_x_bus_evt2 != 0)) && ((_x_bus_evt1 != 0) && ( !(_x_bus_evt0 != 0))))) || (((_x_bus_evt2 != 0) && ((_x_bus_evt1 != 0) && ( !(_x_bus_evt0 != 0)))) || (( !(_x_bus_evt2 != 0)) && ((_x_bus_evt0 != 0) && ( !(_x_bus_evt1 != 0))))))) && (((( !(_x_bus_l0 != 0)) && ( !(_x_bus_l1 != 0))) || ((_x_bus_l1 != 0) && ( !(_x_bus_l0 != 0)))) || (((_x_bus_l0 != 0) && ( !(_x_bus_l1 != 0))) || ((_x_bus_l0 != 0) && (_x_bus_l1 != 0))))) && ((( !(13.0 <= _x_bus_x)) || ( !((_x_bus_l0 != 0) && ( !(_x_bus_l1 != 0))))) && ((_x_delta == 0.0) || ( !((_x_bus_l0 != 0) && (_x_bus_l1 != 0)))))) && ((delta <= 0.0) || (((delta + (bus_x + (-1.0 * _x_bus_x))) == 0.0) && ((((bus_l0 != 0) == (_x_bus_l0 != 0)) && ((bus_l1 != 0) == (_x_bus_l1 != 0))) && (bus_j == _x_bus_j))))) && ((((delta + (bus_x + (-1.0 * _x_bus_x))) == 0.0) && ((((bus_l0 != 0) == (_x_bus_l0 != 0)) && ((bus_l1 != 0) == (_x_bus_l1 != 0))) && (bus_j == _x_bus_j))) || ( !(( !(bus_evt2 != 0)) && (( !(bus_evt0 != 0)) && ( !(bus_evt1 != 0))))))) && (((((bus_evt2 != 0) && (( !(bus_evt0 != 0)) && ( !(bus_evt1 != 0)))) && ((_x_bus_l1 != 0) && ( !(_x_bus_l0 != 0)))) && ((bus_j == _x_bus_j) && (_x_bus_x == 0.0))) || ( !((( !(bus_l0 != 0)) && ( !(bus_l1 != 0))) && ((delta == 0.0) && ( !(( !(bus_evt2 != 0)) && (( !(bus_evt0 != 0)) && ( !(bus_evt1 != 0)))))))))) && (((bus_j == _x_bus_j) && (((_x_bus_l0 != 0) && ( !(_x_bus_l1 != 0))) || ((( !(_x_bus_l0 != 0)) && ( !(_x_bus_l1 != 0))) || ((_x_bus_l1 != 0) && ( !(_x_bus_l0 != 0)))))) || ( !(((bus_l1 != 0) && ( !(bus_l0 != 0))) && ((delta == 0.0) && ( !(( !(bus_evt2 != 0)) && (( !(bus_evt0 != 0)) && ( !(bus_evt1 != 0)))))))))) && (((( !(bus_evt2 != 0)) && ((bus_evt1 != 0) && ( !(bus_evt0 != 0)))) && (_x_bus_x == 0.0)) || ( !(((delta == 0.0) && ( !(( !(bus_evt2 != 0)) && (( !(bus_evt0 != 0)) && ( !(bus_evt1 != 0)))))) && ((( !(_x_bus_l0 != 0)) && ( !(_x_bus_l1 != 0))) && ((bus_l1 != 0) && ( !(bus_l0 != 0)))))))) && ((((bus_evt2 != 0) && ((bus_evt1 != 0) && ( !(bus_evt0 != 0)))) && ((13.0 <= bus_x) && (bus_x == _x_bus_x))) || ( !(((delta == 0.0) && ( !(( !(bus_evt2 != 0)) && (( !(bus_evt0 != 0)) && ( !(bus_evt1 != 0)))))) && (((bus_l1 != 0) && ( !(bus_l0 != 0))) && ((_x_bus_l1 != 0) && ( !(_x_bus_l0 != 0)))))))) && ((((bus_evt2 != 0) && (( !(bus_evt0 != 0)) && ( !(bus_evt1 != 0)))) && (( !(13.0 <= bus_x)) && (_x_bus_x == 0.0))) || ( !(((delta == 0.0) && ( !(( !(bus_evt2 != 0)) && (( !(bus_evt0 != 0)) && ( !(bus_evt1 != 0)))))) && (((bus_l1 != 0) && ( !(bus_l0 != 0))) && ((_x_bus_l0 != 0) && ( !(_x_bus_l1 != 0)))))))) && ((((((_x_bus_l0 != 0) && (_x_bus_l1 != 0)) && ( !(13.0 <= bus_x))) && ((( !(bus_evt2 != 0)) && ((bus_evt0 != 0) && ( !(bus_evt1 != 0)))) && (bus_cd_id == bus_j))) && ((_x_bus_x == 0.0) && ((bus_j + (-1 * _x_bus_j)) == -1))) || ( !(((bus_l0 != 0) && ( !(bus_l1 != 0))) && ((delta == 0.0) && ( !(( !(bus_evt2 != 0)) && (( !(bus_evt0 != 0)) && ( !(bus_evt1 != 0)))))))))) && ((((bus_j + (-1 * _x_bus_j)) == -1) && (((( !(bus_evt2 != 0)) && ((bus_evt0 != 0) && ( !(bus_evt1 != 0)))) && (bus_cd_id == bus_j)) && ((_x_bus_x == 0.0) && ( !(1 <= bus_j))))) || ( !(((delta == 0.0) && ( !(( !(bus_evt2 != 0)) && (( !(bus_evt0 != 0)) && ( !(bus_evt1 != 0)))))) && (((bus_l0 != 0) && (bus_l1 != 0)) && ((_x_bus_l0 != 0) && (_x_bus_l1 != 0))))))) && (((((( !(bus_evt2 != 0)) && ((bus_evt0 != 0) && ( !(bus_evt1 != 0)))) && (bus_j == 1)) && ((_x_bus_x == 0.0) && (bus_cd_id == bus_j))) && (_x_bus_j == 0)) || ( !(((delta == 0.0) && ( !(( !(bus_evt2 != 0)) && (( !(bus_evt0 != 0)) && ( !(bus_evt1 != 0)))))) && ((( !(_x_bus_l0 != 0)) && ( !(_x_bus_l1 != 0))) && ((bus_l0 != 0) && (bus_l1 != 0))))))) && (0.0 <= _x_delta)))) && (((( !(s0_evt2 != 0)) && (( !(s0_evt0 != 0)) && ( !(s0_evt1 != 0)))) || (( !(s1_evt2 != 0)) && (( !(s1_evt0 != 0)) && ( !(s1_evt1 != 0))))) || ( !(delta == 0.0)))) && (( !(delta == 0.0)) || (( !(( !(s1_evt2 != 0)) && (( !(s1_evt0 != 0)) && ( !(s1_evt1 != 0))))) || (( !(( !(bus_evt2 != 0)) && (( !(bus_evt0 != 0)) && ( !(bus_evt1 != 0))))) || ( !(( !(s0_evt2 != 0)) && (( !(s0_evt0 != 0)) && ( !(s0_evt1 != 0))))))))) && (( !(delta == 0.0)) || (((((bus_evt2 != 0) && (( !(bus_evt0 != 0)) && ( !(bus_evt1 != 0)))) == (((s0_evt2 != 0) && (( !(s0_evt0 != 0)) && ( !(s0_evt1 != 0)))) || ((s1_evt2 != 0) && (( !(s1_evt0 != 0)) && ( !(s1_evt1 != 0)))))) && ((( !(bus_evt2 != 0)) && ((bus_evt1 != 0) && ( !(bus_evt0 != 0)))) == ((( !(s0_evt2 != 0)) && ((s0_evt1 != 0) && ( !(s0_evt0 != 0)))) || (( !(s1_evt2 != 0)) && ((s1_evt1 != 0) && ( !(s1_evt0 != 0))))))) && ((((bus_evt2 != 0) && ((bus_evt1 != 0) && ( !(bus_evt0 != 0)))) == (((s0_evt2 != 0) && ((s0_evt1 != 0) && ( !(s0_evt0 != 0)))) || ((s1_evt2 != 0) && ((s1_evt1 != 0) && ( !(s1_evt0 != 0)))))) && ((( !(bus_evt2 != 0)) && ((bus_evt0 != 0) && ( !(bus_evt1 != 0)))) == ((( !(s0_evt2 != 0)) && ((s0_evt0 != 0) && ( !(s0_evt1 != 0)))) || (( !(s1_evt2 != 0)) && ((s1_evt0 != 0) && ( !(s1_evt1 != 0)))))))))) && (( !(delta == 0.0)) || (((( !(s0_evt2 != 0)) && ((s0_evt0 != 0) && ( !(s0_evt1 != 0)))) == ((( !(bus_evt2 != 0)) && ((bus_evt0 != 0) && ( !(bus_evt1 != 0)))) && (bus_cd_id == 0))) && ((( !(s1_evt2 != 0)) && ((s1_evt0 != 0) && ( !(s1_evt1 != 0)))) == ((( !(bus_evt2 != 0)) && ((bus_evt0 != 0) && ( !(bus_evt1 != 0)))) && (bus_cd_id == 1)))))) && (((delta == _x__diverge_delta) || ( !(1.0 <= _diverge_delta))) && ((1.0 <= _diverge_delta) || ((delta + (_diverge_delta + (-1.0 * _x__diverge_delta))) == 0.0))));
    s1_l1 = _x_s1_l1;
    s1_l0 = _x_s1_l0;
    s1_evt2 = _x_s1_evt2;
    s1_evt1 = _x_s1_evt1;
    s1_backoff = _x_s1_backoff;
    s0_l1 = _x_s0_l1;
    _diverge_delta = _x__diverge_delta;
    s0_l0 = _x_s0_l0;
    s0_evt2 = _x_s0_evt2;
    s0_evt1 = _x_s0_evt1;
    s1_x = _x_s1_x;
    bus_j = _x_bus_j;
    s0_x = _x_s0_x;
    s1_lambda = _x_s1_lambda;
    bus_x = _x_bus_x;
    delta = _x_delta;
    s0_lambda = _x_s0_lambda;
    bus_cd_id = _x_bus_cd_id;
    s0_backoff = _x_s0_backoff;
    bus_evt0 = _x_bus_evt0;
    bus_evt1 = _x_bus_evt1;
    bus_l0 = _x_bus_l0;
    s1_evt0 = _x_s1_evt0;
    bus_evt2 = _x_bus_evt2;
    bus_l1 = _x_bus_l1;
    s0_evt0 = _x_s0_evt0;

  }
}
