//@ ltl invariant negative: ( (<> ([] AP((inc_max_prop != 0)))) || (! ([] (<> AP((1.0 <= _diverge_delta))))));

extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);

char __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}


float _diverge_delta, _x__diverge_delta;
char p3_l1, _x_p3_l1;
char p3_l0, _x_p3_l0;
char p3_l3, _x_p3_l3;
char p0_evt, _x_p0_evt;
char p0_l0, _x_p0_l0;
char p3_l2, _x_p3_l2;
float p0_c, _x_p0_c;
float proposed1, _x_proposed1;
char p1_l3, _x_p1_l3;
float proposed0, _x_proposed0;
char p1_l2, _x_p1_l2;
char inc_max_prop, _x_inc_max_prop;
char p1_evt, _x_p1_evt;
char p1_l1, _x_p1_l1;
char p2_l3, _x_p2_l3;
float max_prop, _x_max_prop;
float p1_c, _x_p1_c;
char p1_l0, _x_p1_l0;
char p2_l2, _x_p2_l2;
char v2, _x_v2;
char p2_l1, _x_p2_l1;
int v1, _x_v1;
char p0_l1, _x_p0_l1;
float p2_c, _x_p2_c;
char p2_l0, _x_p2_l0;
float delta, _x_delta;
float proposed3, _x_proposed3;
char p3_evt, _x_p3_evt;
char p2_evt, _x_p2_evt;
char p0_l2, _x_p0_l2;
char p0_l3, _x_p0_l3;
float proposed2, _x_proposed2;
float p3_c, _x_p3_c;

int main()
{
  _diverge_delta = __VERIFIER_nondet_float();
  p3_l1 = __VERIFIER_nondet_bool();
  p3_l0 = __VERIFIER_nondet_bool();
  p3_l3 = __VERIFIER_nondet_bool();
  p0_evt = __VERIFIER_nondet_bool();
  p0_l0 = __VERIFIER_nondet_bool();
  p3_l2 = __VERIFIER_nondet_bool();
  p0_c = __VERIFIER_nondet_float();
  proposed1 = __VERIFIER_nondet_float();
  p1_l3 = __VERIFIER_nondet_bool();
  proposed0 = __VERIFIER_nondet_float();
  p1_l2 = __VERIFIER_nondet_bool();
  inc_max_prop = __VERIFIER_nondet_bool();
  p1_evt = __VERIFIER_nondet_bool();
  p1_l1 = __VERIFIER_nondet_bool();
  p2_l3 = __VERIFIER_nondet_bool();
  max_prop = __VERIFIER_nondet_float();
  p1_c = __VERIFIER_nondet_float();
  p1_l0 = __VERIFIER_nondet_bool();
  p2_l2 = __VERIFIER_nondet_bool();
  v2 = __VERIFIER_nondet_bool();
  p2_l1 = __VERIFIER_nondet_bool();
  v1 = __VERIFIER_nondet_int();
  p0_l1 = __VERIFIER_nondet_bool();
  p2_c = __VERIFIER_nondet_float();
  p2_l0 = __VERIFIER_nondet_bool();
  delta = __VERIFIER_nondet_float();
  proposed3 = __VERIFIER_nondet_float();
  p3_evt = __VERIFIER_nondet_bool();
  p2_evt = __VERIFIER_nondet_bool();
  p0_l2 = __VERIFIER_nondet_bool();
  p0_l3 = __VERIFIER_nondet_bool();
  proposed2 = __VERIFIER_nondet_float();
  p3_c = __VERIFIER_nondet_float();

  int __ok = (((((((p3_l3 != 0) && (( !(p3_l2 != 0)) && (( !(p3_l0 != 0)) && ( !(p3_l1 != 0))))) || ((( !(p3_l3 != 0)) && ((p3_l2 != 0) && ((p3_l0 != 0) && (p3_l1 != 0)))) || ((( !(p3_l3 != 0)) && ((p3_l2 != 0) && ((p3_l1 != 0) && ( !(p3_l0 != 0))))) || ((( !(p3_l3 != 0)) && ((p3_l2 != 0) && ((p3_l0 != 0) && ( !(p3_l1 != 0))))) || ((( !(p3_l3 != 0)) && ((p3_l2 != 0) && (( !(p3_l0 != 0)) && ( !(p3_l1 != 0))))) || ((( !(p3_l3 != 0)) && (( !(p3_l2 != 0)) && ((p3_l0 != 0) && (p3_l1 != 0)))) || ((( !(p3_l3 != 0)) && (( !(p3_l2 != 0)) && ((p3_l1 != 0) && ( !(p3_l0 != 0))))) || ((( !(p3_l3 != 0)) && (( !(p3_l2 != 0)) && (( !(p3_l0 != 0)) && ( !(p3_l1 != 0))))) || (( !(p3_l3 != 0)) && (( !(p3_l2 != 0)) && ((p3_l0 != 0) && ( !(p3_l1 != 0))))))))))))) && ((( !(p3_l3 != 0)) && (( !(p3_l2 != 0)) && (( !(p3_l0 != 0)) && ( !(p3_l1 != 0))))) && (p3_c == 0.0))) && ((p3_c <= proposed3) || ( !(((( !(p3_l3 != 0)) && (( !(p3_l2 != 0)) && ((p3_l0 != 0) && ( !(p3_l1 != 0))))) || (( !(p3_l3 != 0)) && ((p3_l2 != 0) && (( !(p3_l0 != 0)) && ( !(p3_l1 != 0)))))) || ((( !(p3_l3 != 0)) && ((p3_l2 != 0) && ((p3_l0 != 0) && (p3_l1 != 0)))) || ((p3_l3 != 0) && (( !(p3_l2 != 0)) && (( !(p3_l0 != 0)) && ( !(p3_l1 != 0)))))))))) && ((((((p2_l3 != 0) && (( !(p2_l2 != 0)) && (( !(p2_l0 != 0)) && ( !(p2_l1 != 0))))) || ((( !(p2_l3 != 0)) && ((p2_l2 != 0) && ((p2_l0 != 0) && (p2_l1 != 0)))) || ((( !(p2_l3 != 0)) && ((p2_l2 != 0) && ((p2_l1 != 0) && ( !(p2_l0 != 0))))) || ((( !(p2_l3 != 0)) && ((p2_l2 != 0) && ((p2_l0 != 0) && ( !(p2_l1 != 0))))) || ((( !(p2_l3 != 0)) && ((p2_l2 != 0) && (( !(p2_l0 != 0)) && ( !(p2_l1 != 0))))) || ((( !(p2_l3 != 0)) && (( !(p2_l2 != 0)) && ((p2_l0 != 0) && (p2_l1 != 0)))) || ((( !(p2_l3 != 0)) && (( !(p2_l2 != 0)) && ((p2_l1 != 0) && ( !(p2_l0 != 0))))) || ((( !(p2_l3 != 0)) && (( !(p2_l2 != 0)) && (( !(p2_l0 != 0)) && ( !(p2_l1 != 0))))) || (( !(p2_l3 != 0)) && (( !(p2_l2 != 0)) && ((p2_l0 != 0) && ( !(p2_l1 != 0))))))))))))) && ((( !(p2_l3 != 0)) && (( !(p2_l2 != 0)) && (( !(p2_l0 != 0)) && ( !(p2_l1 != 0))))) && (p2_c == 0.0))) && ((p2_c <= proposed2) || ( !(((( !(p2_l3 != 0)) && (( !(p2_l2 != 0)) && ((p2_l0 != 0) && ( !(p2_l1 != 0))))) || (( !(p2_l3 != 0)) && ((p2_l2 != 0) && (( !(p2_l0 != 0)) && ( !(p2_l1 != 0)))))) || ((( !(p2_l3 != 0)) && ((p2_l2 != 0) && ((p2_l0 != 0) && (p2_l1 != 0)))) || ((p2_l3 != 0) && (( !(p2_l2 != 0)) && (( !(p2_l0 != 0)) && ( !(p2_l1 != 0)))))))))) && ((((((p1_l3 != 0) && (( !(p1_l2 != 0)) && (( !(p1_l0 != 0)) && ( !(p1_l1 != 0))))) || ((( !(p1_l3 != 0)) && ((p1_l2 != 0) && ((p1_l0 != 0) && (p1_l1 != 0)))) || ((( !(p1_l3 != 0)) && ((p1_l2 != 0) && ((p1_l1 != 0) && ( !(p1_l0 != 0))))) || ((( !(p1_l3 != 0)) && ((p1_l2 != 0) && ((p1_l0 != 0) && ( !(p1_l1 != 0))))) || ((( !(p1_l3 != 0)) && ((p1_l2 != 0) && (( !(p1_l0 != 0)) && ( !(p1_l1 != 0))))) || ((( !(p1_l3 != 0)) && (( !(p1_l2 != 0)) && ((p1_l0 != 0) && (p1_l1 != 0)))) || ((( !(p1_l3 != 0)) && (( !(p1_l2 != 0)) && ((p1_l1 != 0) && ( !(p1_l0 != 0))))) || ((( !(p1_l3 != 0)) && (( !(p1_l2 != 0)) && (( !(p1_l0 != 0)) && ( !(p1_l1 != 0))))) || (( !(p1_l3 != 0)) && (( !(p1_l2 != 0)) && ((p1_l0 != 0) && ( !(p1_l1 != 0))))))))))))) && ((( !(p1_l3 != 0)) && (( !(p1_l2 != 0)) && (( !(p1_l0 != 0)) && ( !(p1_l1 != 0))))) && (p1_c == 0.0))) && ((p1_c <= proposed1) || ( !(((( !(p1_l3 != 0)) && (( !(p1_l2 != 0)) && ((p1_l0 != 0) && ( !(p1_l1 != 0))))) || (( !(p1_l3 != 0)) && ((p1_l2 != 0) && (( !(p1_l0 != 0)) && ( !(p1_l1 != 0)))))) || ((( !(p1_l3 != 0)) && ((p1_l2 != 0) && ((p1_l0 != 0) && (p1_l1 != 0)))) || ((p1_l3 != 0) && (( !(p1_l2 != 0)) && (( !(p1_l0 != 0)) && ( !(p1_l1 != 0)))))))))) && ((((((p0_l3 != 0) && (( !(p0_l2 != 0)) && (( !(p0_l0 != 0)) && ( !(p0_l1 != 0))))) || ((( !(p0_l3 != 0)) && ((p0_l2 != 0) && ((p0_l0 != 0) && (p0_l1 != 0)))) || ((( !(p0_l3 != 0)) && ((p0_l2 != 0) && ((p0_l1 != 0) && ( !(p0_l0 != 0))))) || ((( !(p0_l3 != 0)) && ((p0_l2 != 0) && ((p0_l0 != 0) && ( !(p0_l1 != 0))))) || ((( !(p0_l3 != 0)) && ((p0_l2 != 0) && (( !(p0_l0 != 0)) && ( !(p0_l1 != 0))))) || ((( !(p0_l3 != 0)) && (( !(p0_l2 != 0)) && ((p0_l0 != 0) && (p0_l1 != 0)))) || ((( !(p0_l3 != 0)) && (( !(p0_l2 != 0)) && ((p0_l1 != 0) && ( !(p0_l0 != 0))))) || ((( !(p0_l3 != 0)) && (( !(p0_l2 != 0)) && (( !(p0_l0 != 0)) && ( !(p0_l1 != 0))))) || (( !(p0_l3 != 0)) && (( !(p0_l2 != 0)) && ((p0_l0 != 0) && ( !(p0_l1 != 0))))))))))))) && ((( !(p0_l3 != 0)) && (( !(p0_l2 != 0)) && (( !(p0_l0 != 0)) && ( !(p0_l1 != 0))))) && (p0_c == 0.0))) && ((p0_c <= proposed0) || ( !(((( !(p0_l3 != 0)) && (( !(p0_l2 != 0)) && ((p0_l0 != 0) && ( !(p0_l1 != 0))))) || (( !(p0_l3 != 0)) && ((p0_l2 != 0) && (( !(p0_l0 != 0)) && ( !(p0_l1 != 0)))))) || ((( !(p0_l3 != 0)) && ((p0_l2 != 0) && ((p0_l0 != 0) && (p0_l1 != 0)))) || ((p0_l3 != 0) && (( !(p0_l2 != 0)) && (( !(p0_l0 != 0)) && ( !(p0_l1 != 0)))))))))) && ((((((((((((inc_max_prop != 0) && ((v1 == 4) || ((v1 == 3) || ((v1 == 2) || ((v1 == 0) || (v1 == 1)))))) && (proposed0 == 16.0)) && (proposed1 == 16.0)) && (proposed2 == 16.0)) && (proposed3 == 16.0)) && (0.0 <= delta)) && (( !(proposed0 <= 0.0)) && (proposed0 <= max_prop))) && (( !(proposed1 <= 0.0)) && (proposed1 <= max_prop))) && (( !(proposed2 <= 0.0)) && (proposed2 <= max_prop))) && (( !(proposed3 <= 0.0)) && (proposed3 <= max_prop))) && ((((max_prop == proposed0) || (max_prop == proposed1)) || (max_prop == proposed2)) || (max_prop == proposed3))))))) && (delta == _diverge_delta));
  while (__ok) {
    _x__diverge_delta = __VERIFIER_nondet_float();
    _x_p3_l1 = __VERIFIER_nondet_bool();
    _x_p3_l0 = __VERIFIER_nondet_bool();
    _x_p3_l3 = __VERIFIER_nondet_bool();
    _x_p0_evt = __VERIFIER_nondet_bool();
    _x_p0_l0 = __VERIFIER_nondet_bool();
    _x_p3_l2 = __VERIFIER_nondet_bool();
    _x_p0_c = __VERIFIER_nondet_float();
    _x_proposed1 = __VERIFIER_nondet_float();
    _x_p1_l3 = __VERIFIER_nondet_bool();
    _x_proposed0 = __VERIFIER_nondet_float();
    _x_p1_l2 = __VERIFIER_nondet_bool();
    _x_inc_max_prop = __VERIFIER_nondet_bool();
    _x_p1_evt = __VERIFIER_nondet_bool();
    _x_p1_l1 = __VERIFIER_nondet_bool();
    _x_p2_l3 = __VERIFIER_nondet_bool();
    _x_max_prop = __VERIFIER_nondet_float();
    _x_p1_c = __VERIFIER_nondet_float();
    _x_p1_l0 = __VERIFIER_nondet_bool();
    _x_p2_l2 = __VERIFIER_nondet_bool();
    _x_v2 = __VERIFIER_nondet_bool();
    _x_p2_l1 = __VERIFIER_nondet_bool();
    _x_v1 = __VERIFIER_nondet_int();
    _x_p0_l1 = __VERIFIER_nondet_bool();
    _x_p2_c = __VERIFIER_nondet_float();
    _x_p2_l0 = __VERIFIER_nondet_bool();
    _x_delta = __VERIFIER_nondet_float();
    _x_proposed3 = __VERIFIER_nondet_float();
    _x_p3_evt = __VERIFIER_nondet_bool();
    _x_p2_evt = __VERIFIER_nondet_bool();
    _x_p0_l2 = __VERIFIER_nondet_bool();
    _x_p0_l3 = __VERIFIER_nondet_bool();
    _x_proposed2 = __VERIFIER_nondet_float();
    _x_p3_c = __VERIFIER_nondet_float();

    __ok = (((((((((((((((((((((((((_x_p3_l3 != 0) && (( !(_x_p3_l2 != 0)) && (( !(_x_p3_l0 != 0)) && ( !(_x_p3_l1 != 0))))) || ((( !(_x_p3_l3 != 0)) && ((_x_p3_l2 != 0) && ((_x_p3_l0 != 0) && (_x_p3_l1 != 0)))) || ((( !(_x_p3_l3 != 0)) && ((_x_p3_l2 != 0) && ((_x_p3_l1 != 0) && ( !(_x_p3_l0 != 0))))) || ((( !(_x_p3_l3 != 0)) && ((_x_p3_l2 != 0) && ((_x_p3_l0 != 0) && ( !(_x_p3_l1 != 0))))) || ((( !(_x_p3_l3 != 0)) && ((_x_p3_l2 != 0) && (( !(_x_p3_l0 != 0)) && ( !(_x_p3_l1 != 0))))) || ((( !(_x_p3_l3 != 0)) && (( !(_x_p3_l2 != 0)) && ((_x_p3_l0 != 0) && (_x_p3_l1 != 0)))) || ((( !(_x_p3_l3 != 0)) && (( !(_x_p3_l2 != 0)) && ((_x_p3_l1 != 0) && ( !(_x_p3_l0 != 0))))) || ((( !(_x_p3_l3 != 0)) && (( !(_x_p3_l2 != 0)) && (( !(_x_p3_l0 != 0)) && ( !(_x_p3_l1 != 0))))) || (( !(_x_p3_l3 != 0)) && (( !(_x_p3_l2 != 0)) && ((_x_p3_l0 != 0) && ( !(_x_p3_l1 != 0))))))))))))) && ((_x_p3_c <= _x_proposed3) || ( !(((( !(_x_p3_l3 != 0)) && (( !(_x_p3_l2 != 0)) && ((_x_p3_l0 != 0) && ( !(_x_p3_l1 != 0))))) || (( !(_x_p3_l3 != 0)) && ((_x_p3_l2 != 0) && (( !(_x_p3_l0 != 0)) && ( !(_x_p3_l1 != 0)))))) || ((( !(_x_p3_l3 != 0)) && ((_x_p3_l2 != 0) && ((_x_p3_l0 != 0) && (_x_p3_l1 != 0)))) || ((_x_p3_l3 != 0) && (( !(_x_p3_l2 != 0)) && (( !(_x_p3_l0 != 0)) && ( !(_x_p3_l1 != 0)))))))))) && ((((((((p3_l0 != 0) == (_x_p3_l0 != 0)) && ((p3_l1 != 0) == (_x_p3_l1 != 0))) && ((p3_l2 != 0) == (_x_p3_l2 != 0))) && ((p3_l3 != 0) == (_x_p3_l3 != 0))) && ((delta + (p3_c + (-1.0 * _x_p3_c))) == 0.0)) && (proposed3 == _x_proposed3)) || ( !(( !(delta <= 0.0)) || ( !(p3_evt != 0)))))) && (((((v1 == 0) && (( !(_x_p3_l3 != 0)) && (( !(_x_p3_l2 != 0)) && ((_x_p3_l0 != 0) && ( !(_x_p3_l1 != 0)))))) && (((v2 != 0) == (_x_v2 != 0)) && (_x_p3_c == 0.0))) && ((v1 == _x_v1) && (proposed3 == _x_proposed3))) || ( !((( !(p3_l3 != 0)) && (( !(p3_l2 != 0)) && (( !(p3_l0 != 0)) && ( !(p3_l1 != 0))))) && ((delta == 0.0) && (p3_evt != 0)))))) && (((proposed3 == _x_proposed3) && ((((v2 != 0) == (_x_v2 != 0)) && (_x_p3_c == 0.0)) && ((( !(_x_p3_l3 != 0)) && (( !(_x_p3_l2 != 0)) && ((_x_p3_l1 != 0) && ( !(_x_p3_l0 != 0))))) && (_x_v1 == 4)))) || ( !((( !(p3_l3 != 0)) && (( !(p3_l2 != 0)) && ((p3_l0 != 0) && ( !(p3_l1 != 0))))) && ((delta == 0.0) && (p3_evt != 0)))))) && (((((v2 != 0) == (_x_v2 != 0)) && (v1 == _x_v1)) && (((( !(_x_p3_l3 != 0)) && (( !(_x_p3_l2 != 0)) && (( !(_x_p3_l0 != 0)) && ( !(_x_p3_l1 != 0))))) || (( !(_x_p3_l3 != 0)) && (( !(_x_p3_l2 != 0)) && ((_x_p3_l0 != 0) && (_x_p3_l1 != 0))))) && (p3_c == _x_p3_c))) || ( !((( !(p3_l3 != 0)) && (( !(p3_l2 != 0)) && ((p3_l1 != 0) && ( !(p3_l0 != 0))))) && ((delta == 0.0) && (p3_evt != 0)))))) && (((proposed3 == _x_proposed3) && ( !(v1 == 4))) || ( !(((delta == 0.0) && (p3_evt != 0)) && ((( !(_x_p3_l3 != 0)) && (( !(_x_p3_l2 != 0)) && (( !(_x_p3_l0 != 0)) && ( !(_x_p3_l1 != 0))))) && (( !(p3_l3 != 0)) && (( !(p3_l2 != 0)) && ((p3_l1 != 0) && ( !(p3_l0 != 0)))))))))) && ((((v1 == 4) && ( !(p3_c <= max_prop))) && ( !(proposed3 <= _x_proposed3))) || ( !(((delta == 0.0) && (p3_evt != 0)) && ((( !(p3_l3 != 0)) && (( !(p3_l2 != 0)) && ((p3_l1 != 0) && ( !(p3_l0 != 0))))) && (( !(_x_p3_l3 != 0)) && (( !(_x_p3_l2 != 0)) && ((_x_p3_l0 != 0) && (_x_p3_l1 != 0))))))))) && (((((v2 != 0) == (_x_v2 != 0)) && (v1 == _x_v1)) && ((proposed3 == _x_proposed3) && ((( !(_x_p3_l3 != 0)) && (( !(_x_p3_l2 != 0)) && (( !(_x_p3_l0 != 0)) && ( !(_x_p3_l1 != 0))))) || (( !(_x_p3_l3 != 0)) && ((_x_p3_l2 != 0) && (( !(_x_p3_l0 != 0)) && ( !(_x_p3_l1 != 0)))))))) || ( !((( !(p3_l3 != 0)) && (( !(p3_l2 != 0)) && ((p3_l0 != 0) && (p3_l1 != 0)))) && ((delta == 0.0) && (p3_evt != 0)))))) && (((v2 != 0) && (p3_c == _x_p3_c)) || ( !(((delta == 0.0) && (p3_evt != 0)) && ((( !(_x_p3_l3 != 0)) && (( !(_x_p3_l2 != 0)) && (( !(_x_p3_l0 != 0)) && ( !(_x_p3_l1 != 0))))) && (( !(p3_l3 != 0)) && (( !(p3_l2 != 0)) && ((p3_l0 != 0) && (p3_l1 != 0))))))))) && ((( !(v2 != 0)) && (_x_p3_c == 0.0)) || ( !(((delta == 0.0) && (p3_evt != 0)) && ((( !(p3_l3 != 0)) && (( !(p3_l2 != 0)) && ((p3_l0 != 0) && (p3_l1 != 0)))) && (( !(_x_p3_l3 != 0)) && ((_x_p3_l2 != 0) && (( !(_x_p3_l0 != 0)) && ( !(_x_p3_l1 != 0)))))))))) && ((((v1 == _x_v1) && (proposed3 == _x_proposed3)) && ((_x_p3_c == 0.0) && ((_x_v2 != 0) && (( !(_x_p3_l3 != 0)) && ((_x_p3_l2 != 0) && ((_x_p3_l0 != 0) && ( !(_x_p3_l1 != 0)))))))) || ( !((( !(p3_l3 != 0)) && ((p3_l2 != 0) && (( !(p3_l0 != 0)) && ( !(p3_l1 != 0))))) && ((delta == 0.0) && (p3_evt != 0)))))) && (((proposed3 == _x_proposed3) && ((((v2 != 0) == (_x_v2 != 0)) && (v1 == _x_v1)) && ((p3_c == _x_p3_c) && ((( !(_x_p3_l3 != 0)) && (( !(_x_p3_l2 != 0)) && (( !(_x_p3_l0 != 0)) && ( !(_x_p3_l1 != 0))))) || (( !(_x_p3_l3 != 0)) && ((_x_p3_l2 != 0) && ((_x_p3_l1 != 0) && ( !(_x_p3_l0 != 0))))))))) || ( !((( !(p3_l3 != 0)) && ((p3_l2 != 0) && ((p3_l0 != 0) && ( !(p3_l1 != 0))))) && ((delta == 0.0) && (p3_evt != 0)))))) && (( !(v1 == 4)) || ( !(((delta == 0.0) && (p3_evt != 0)) && ((( !(_x_p3_l3 != 0)) && (( !(_x_p3_l2 != 0)) && (( !(_x_p3_l0 != 0)) && ( !(_x_p3_l1 != 0))))) && (( !(p3_l3 != 0)) && ((p3_l2 != 0) && ((p3_l0 != 0) && ( !(p3_l1 != 0)))))))))) && ((v1 == 4) || ( !(((delta == 0.0) && (p3_evt != 0)) && ((( !(p3_l3 != 0)) && ((p3_l2 != 0) && ((p3_l0 != 0) && ( !(p3_l1 != 0))))) && (( !(_x_p3_l3 != 0)) && ((_x_p3_l2 != 0) && ((_x_p3_l1 != 0) && ( !(_x_p3_l0 != 0)))))))))) && (((proposed3 == _x_proposed3) && ((((v2 != 0) == (_x_v2 != 0)) && (v1 == _x_v1)) && ((( !(_x_p3_l3 != 0)) && ((_x_p3_l2 != 0) && ((_x_p3_l0 != 0) && (_x_p3_l1 != 0)))) && (_x_p3_c == 0.0)))) || ( !((( !(p3_l3 != 0)) && ((p3_l2 != 0) && ((p3_l1 != 0) && ( !(p3_l0 != 0))))) && ((delta == 0.0) && (p3_evt != 0)))))) && (((proposed3 == _x_proposed3) && ((( !(_x_v2 != 0)) && ((_x_p3_l3 != 0) && (( !(_x_p3_l2 != 0)) && (( !(_x_p3_l0 != 0)) && ( !(_x_p3_l1 != 0)))))) && ((v1 == _x_v1) && (_x_p3_c == 0.0)))) || ( !((( !(p3_l3 != 0)) && ((p3_l2 != 0) && ((p3_l0 != 0) && (p3_l1 != 0)))) && ((delta == 0.0) && (p3_evt != 0)))))) && (((proposed3 == _x_proposed3) && (((_x_v1 == 0) && (( !(_x_p3_l3 != 0)) && (( !(_x_p3_l2 != 0)) && (( !(_x_p3_l0 != 0)) && ( !(_x_p3_l1 != 0)))))) && (((v2 != 0) == (_x_v2 != 0)) && (p3_c == _x_p3_c)))) || ( !(((p3_l3 != 0) && (( !(p3_l2 != 0)) && (( !(p3_l0 != 0)) && ( !(p3_l1 != 0))))) && ((delta == 0.0) && (p3_evt != 0)))))) && (((((((((((((((((((((_x_p2_l3 != 0) && (( !(_x_p2_l2 != 0)) && (( !(_x_p2_l0 != 0)) && ( !(_x_p2_l1 != 0))))) || ((( !(_x_p2_l3 != 0)) && ((_x_p2_l2 != 0) && ((_x_p2_l0 != 0) && (_x_p2_l1 != 0)))) || ((( !(_x_p2_l3 != 0)) && ((_x_p2_l2 != 0) && ((_x_p2_l1 != 0) && ( !(_x_p2_l0 != 0))))) || ((( !(_x_p2_l3 != 0)) && ((_x_p2_l2 != 0) && ((_x_p2_l0 != 0) && ( !(_x_p2_l1 != 0))))) || ((( !(_x_p2_l3 != 0)) && ((_x_p2_l2 != 0) && (( !(_x_p2_l0 != 0)) && ( !(_x_p2_l1 != 0))))) || ((( !(_x_p2_l3 != 0)) && (( !(_x_p2_l2 != 0)) && ((_x_p2_l0 != 0) && (_x_p2_l1 != 0)))) || ((( !(_x_p2_l3 != 0)) && (( !(_x_p2_l2 != 0)) && ((_x_p2_l1 != 0) && ( !(_x_p2_l0 != 0))))) || ((( !(_x_p2_l3 != 0)) && (( !(_x_p2_l2 != 0)) && (( !(_x_p2_l0 != 0)) && ( !(_x_p2_l1 != 0))))) || (( !(_x_p2_l3 != 0)) && (( !(_x_p2_l2 != 0)) && ((_x_p2_l0 != 0) && ( !(_x_p2_l1 != 0))))))))))))) && ((_x_p2_c <= _x_proposed2) || ( !(((( !(_x_p2_l3 != 0)) && (( !(_x_p2_l2 != 0)) && ((_x_p2_l0 != 0) && ( !(_x_p2_l1 != 0))))) || (( !(_x_p2_l3 != 0)) && ((_x_p2_l2 != 0) && (( !(_x_p2_l0 != 0)) && ( !(_x_p2_l1 != 0)))))) || ((( !(_x_p2_l3 != 0)) && ((_x_p2_l2 != 0) && ((_x_p2_l0 != 0) && (_x_p2_l1 != 0)))) || ((_x_p2_l3 != 0) && (( !(_x_p2_l2 != 0)) && (( !(_x_p2_l0 != 0)) && ( !(_x_p2_l1 != 0)))))))))) && ((((((((p2_l0 != 0) == (_x_p2_l0 != 0)) && ((p2_l1 != 0) == (_x_p2_l1 != 0))) && ((p2_l2 != 0) == (_x_p2_l2 != 0))) && ((p2_l3 != 0) == (_x_p2_l3 != 0))) && ((delta + (p2_c + (-1.0 * _x_p2_c))) == 0.0)) && (proposed2 == _x_proposed2)) || ( !(( !(delta <= 0.0)) || ( !(p2_evt != 0)))))) && (((((v1 == 0) && (( !(_x_p2_l3 != 0)) && (( !(_x_p2_l2 != 0)) && ((_x_p2_l0 != 0) && ( !(_x_p2_l1 != 0)))))) && (((v2 != 0) == (_x_v2 != 0)) && (_x_p2_c == 0.0))) && ((v1 == _x_v1) && (proposed2 == _x_proposed2))) || ( !((( !(p2_l3 != 0)) && (( !(p2_l2 != 0)) && (( !(p2_l0 != 0)) && ( !(p2_l1 != 0))))) && ((delta == 0.0) && (p2_evt != 0)))))) && (((proposed2 == _x_proposed2) && ((((v2 != 0) == (_x_v2 != 0)) && (_x_p2_c == 0.0)) && ((( !(_x_p2_l3 != 0)) && (( !(_x_p2_l2 != 0)) && ((_x_p2_l1 != 0) && ( !(_x_p2_l0 != 0))))) && (_x_v1 == 3)))) || ( !((( !(p2_l3 != 0)) && (( !(p2_l2 != 0)) && ((p2_l0 != 0) && ( !(p2_l1 != 0))))) && ((delta == 0.0) && (p2_evt != 0)))))) && (((((v2 != 0) == (_x_v2 != 0)) && (v1 == _x_v1)) && (((( !(_x_p2_l3 != 0)) && (( !(_x_p2_l2 != 0)) && (( !(_x_p2_l0 != 0)) && ( !(_x_p2_l1 != 0))))) || (( !(_x_p2_l3 != 0)) && (( !(_x_p2_l2 != 0)) && ((_x_p2_l0 != 0) && (_x_p2_l1 != 0))))) && (p2_c == _x_p2_c))) || ( !((( !(p2_l3 != 0)) && (( !(p2_l2 != 0)) && ((p2_l1 != 0) && ( !(p2_l0 != 0))))) && ((delta == 0.0) && (p2_evt != 0)))))) && (((proposed2 == _x_proposed2) && ( !(v1 == 3))) || ( !(((delta == 0.0) && (p2_evt != 0)) && ((( !(_x_p2_l3 != 0)) && (( !(_x_p2_l2 != 0)) && (( !(_x_p2_l0 != 0)) && ( !(_x_p2_l1 != 0))))) && (( !(p2_l3 != 0)) && (( !(p2_l2 != 0)) && ((p2_l1 != 0) && ( !(p2_l0 != 0)))))))))) && ((((v1 == 3) && ( !(p2_c <= max_prop))) && ( !(proposed2 <= _x_proposed2))) || ( !(((delta == 0.0) && (p2_evt != 0)) && ((( !(p2_l3 != 0)) && (( !(p2_l2 != 0)) && ((p2_l1 != 0) && ( !(p2_l0 != 0))))) && (( !(_x_p2_l3 != 0)) && (( !(_x_p2_l2 != 0)) && ((_x_p2_l0 != 0) && (_x_p2_l1 != 0))))))))) && (((((v2 != 0) == (_x_v2 != 0)) && (v1 == _x_v1)) && ((proposed2 == _x_proposed2) && ((( !(_x_p2_l3 != 0)) && (( !(_x_p2_l2 != 0)) && (( !(_x_p2_l0 != 0)) && ( !(_x_p2_l1 != 0))))) || (( !(_x_p2_l3 != 0)) && ((_x_p2_l2 != 0) && (( !(_x_p2_l0 != 0)) && ( !(_x_p2_l1 != 0)))))))) || ( !((( !(p2_l3 != 0)) && (( !(p2_l2 != 0)) && ((p2_l0 != 0) && (p2_l1 != 0)))) && ((delta == 0.0) && (p2_evt != 0)))))) && (((v2 != 0) && (p2_c == _x_p2_c)) || ( !(((delta == 0.0) && (p2_evt != 0)) && ((( !(_x_p2_l3 != 0)) && (( !(_x_p2_l2 != 0)) && (( !(_x_p2_l0 != 0)) && ( !(_x_p2_l1 != 0))))) && (( !(p2_l3 != 0)) && (( !(p2_l2 != 0)) && ((p2_l0 != 0) && (p2_l1 != 0))))))))) && ((( !(v2 != 0)) && (_x_p2_c == 0.0)) || ( !(((delta == 0.0) && (p2_evt != 0)) && ((( !(p2_l3 != 0)) && (( !(p2_l2 != 0)) && ((p2_l0 != 0) && (p2_l1 != 0)))) && (( !(_x_p2_l3 != 0)) && ((_x_p2_l2 != 0) && (( !(_x_p2_l0 != 0)) && ( !(_x_p2_l1 != 0)))))))))) && ((((v1 == _x_v1) && (proposed2 == _x_proposed2)) && ((_x_p2_c == 0.0) && ((_x_v2 != 0) && (( !(_x_p2_l3 != 0)) && ((_x_p2_l2 != 0) && ((_x_p2_l0 != 0) && ( !(_x_p2_l1 != 0)))))))) || ( !((( !(p2_l3 != 0)) && ((p2_l2 != 0) && (( !(p2_l0 != 0)) && ( !(p2_l1 != 0))))) && ((delta == 0.0) && (p2_evt != 0)))))) && (((proposed2 == _x_proposed2) && ((((v2 != 0) == (_x_v2 != 0)) && (v1 == _x_v1)) && ((p2_c == _x_p2_c) && ((( !(_x_p2_l3 != 0)) && (( !(_x_p2_l2 != 0)) && (( !(_x_p2_l0 != 0)) && ( !(_x_p2_l1 != 0))))) || (( !(_x_p2_l3 != 0)) && ((_x_p2_l2 != 0) && ((_x_p2_l1 != 0) && ( !(_x_p2_l0 != 0))))))))) || ( !((( !(p2_l3 != 0)) && ((p2_l2 != 0) && ((p2_l0 != 0) && ( !(p2_l1 != 0))))) && ((delta == 0.0) && (p2_evt != 0)))))) && (( !(v1 == 3)) || ( !(((delta == 0.0) && (p2_evt != 0)) && ((( !(_x_p2_l3 != 0)) && (( !(_x_p2_l2 != 0)) && (( !(_x_p2_l0 != 0)) && ( !(_x_p2_l1 != 0))))) && (( !(p2_l3 != 0)) && ((p2_l2 != 0) && ((p2_l0 != 0) && ( !(p2_l1 != 0)))))))))) && ((v1 == 3) || ( !(((delta == 0.0) && (p2_evt != 0)) && ((( !(p2_l3 != 0)) && ((p2_l2 != 0) && ((p2_l0 != 0) && ( !(p2_l1 != 0))))) && (( !(_x_p2_l3 != 0)) && ((_x_p2_l2 != 0) && ((_x_p2_l1 != 0) && ( !(_x_p2_l0 != 0)))))))))) && (((proposed2 == _x_proposed2) && ((((v2 != 0) == (_x_v2 != 0)) && (v1 == _x_v1)) && ((( !(_x_p2_l3 != 0)) && ((_x_p2_l2 != 0) && ((_x_p2_l0 != 0) && (_x_p2_l1 != 0)))) && (_x_p2_c == 0.0)))) || ( !((( !(p2_l3 != 0)) && ((p2_l2 != 0) && ((p2_l1 != 0) && ( !(p2_l0 != 0))))) && ((delta == 0.0) && (p2_evt != 0)))))) && (((proposed2 == _x_proposed2) && ((( !(_x_v2 != 0)) && ((_x_p2_l3 != 0) && (( !(_x_p2_l2 != 0)) && (( !(_x_p2_l0 != 0)) && ( !(_x_p2_l1 != 0)))))) && ((v1 == _x_v1) && (_x_p2_c == 0.0)))) || ( !((( !(p2_l3 != 0)) && ((p2_l2 != 0) && ((p2_l0 != 0) && (p2_l1 != 0)))) && ((delta == 0.0) && (p2_evt != 0)))))) && (((proposed2 == _x_proposed2) && (((_x_v1 == 0) && (( !(_x_p2_l3 != 0)) && (( !(_x_p2_l2 != 0)) && (( !(_x_p2_l0 != 0)) && ( !(_x_p2_l1 != 0)))))) && (((v2 != 0) == (_x_v2 != 0)) && (p2_c == _x_p2_c)))) || ( !(((p2_l3 != 0) && (( !(p2_l2 != 0)) && (( !(p2_l0 != 0)) && ( !(p2_l1 != 0))))) && ((delta == 0.0) && (p2_evt != 0)))))) && (((((((((((((((((((((_x_p1_l3 != 0) && (( !(_x_p1_l2 != 0)) && (( !(_x_p1_l0 != 0)) && ( !(_x_p1_l1 != 0))))) || ((( !(_x_p1_l3 != 0)) && ((_x_p1_l2 != 0) && ((_x_p1_l0 != 0) && (_x_p1_l1 != 0)))) || ((( !(_x_p1_l3 != 0)) && ((_x_p1_l2 != 0) && ((_x_p1_l1 != 0) && ( !(_x_p1_l0 != 0))))) || ((( !(_x_p1_l3 != 0)) && ((_x_p1_l2 != 0) && ((_x_p1_l0 != 0) && ( !(_x_p1_l1 != 0))))) || ((( !(_x_p1_l3 != 0)) && ((_x_p1_l2 != 0) && (( !(_x_p1_l0 != 0)) && ( !(_x_p1_l1 != 0))))) || ((( !(_x_p1_l3 != 0)) && (( !(_x_p1_l2 != 0)) && ((_x_p1_l0 != 0) && (_x_p1_l1 != 0)))) || ((( !(_x_p1_l3 != 0)) && (( !(_x_p1_l2 != 0)) && ((_x_p1_l1 != 0) && ( !(_x_p1_l0 != 0))))) || ((( !(_x_p1_l3 != 0)) && (( !(_x_p1_l2 != 0)) && (( !(_x_p1_l0 != 0)) && ( !(_x_p1_l1 != 0))))) || (( !(_x_p1_l3 != 0)) && (( !(_x_p1_l2 != 0)) && ((_x_p1_l0 != 0) && ( !(_x_p1_l1 != 0))))))))))))) && ((_x_p1_c <= _x_proposed1) || ( !(((( !(_x_p1_l3 != 0)) && (( !(_x_p1_l2 != 0)) && ((_x_p1_l0 != 0) && ( !(_x_p1_l1 != 0))))) || (( !(_x_p1_l3 != 0)) && ((_x_p1_l2 != 0) && (( !(_x_p1_l0 != 0)) && ( !(_x_p1_l1 != 0)))))) || ((( !(_x_p1_l3 != 0)) && ((_x_p1_l2 != 0) && ((_x_p1_l0 != 0) && (_x_p1_l1 != 0)))) || ((_x_p1_l3 != 0) && (( !(_x_p1_l2 != 0)) && (( !(_x_p1_l0 != 0)) && ( !(_x_p1_l1 != 0)))))))))) && ((((((((p1_l0 != 0) == (_x_p1_l0 != 0)) && ((p1_l1 != 0) == (_x_p1_l1 != 0))) && ((p1_l2 != 0) == (_x_p1_l2 != 0))) && ((p1_l3 != 0) == (_x_p1_l3 != 0))) && ((delta + (p1_c + (-1.0 * _x_p1_c))) == 0.0)) && (proposed1 == _x_proposed1)) || ( !(( !(delta <= 0.0)) || ( !(p1_evt != 0)))))) && (((((v1 == 0) && (( !(_x_p1_l3 != 0)) && (( !(_x_p1_l2 != 0)) && ((_x_p1_l0 != 0) && ( !(_x_p1_l1 != 0)))))) && (((v2 != 0) == (_x_v2 != 0)) && (_x_p1_c == 0.0))) && ((v1 == _x_v1) && (proposed1 == _x_proposed1))) || ( !((( !(p1_l3 != 0)) && (( !(p1_l2 != 0)) && (( !(p1_l0 != 0)) && ( !(p1_l1 != 0))))) && ((delta == 0.0) && (p1_evt != 0)))))) && (((proposed1 == _x_proposed1) && ((((v2 != 0) == (_x_v2 != 0)) && (_x_p1_c == 0.0)) && ((( !(_x_p1_l3 != 0)) && (( !(_x_p1_l2 != 0)) && ((_x_p1_l1 != 0) && ( !(_x_p1_l0 != 0))))) && (_x_v1 == 2)))) || ( !((( !(p1_l3 != 0)) && (( !(p1_l2 != 0)) && ((p1_l0 != 0) && ( !(p1_l1 != 0))))) && ((delta == 0.0) && (p1_evt != 0)))))) && (((((v2 != 0) == (_x_v2 != 0)) && (v1 == _x_v1)) && (((( !(_x_p1_l3 != 0)) && (( !(_x_p1_l2 != 0)) && (( !(_x_p1_l0 != 0)) && ( !(_x_p1_l1 != 0))))) || (( !(_x_p1_l3 != 0)) && (( !(_x_p1_l2 != 0)) && ((_x_p1_l0 != 0) && (_x_p1_l1 != 0))))) && (p1_c == _x_p1_c))) || ( !((( !(p1_l3 != 0)) && (( !(p1_l2 != 0)) && ((p1_l1 != 0) && ( !(p1_l0 != 0))))) && ((delta == 0.0) && (p1_evt != 0)))))) && (((proposed1 == _x_proposed1) && ( !(v1 == 2))) || ( !(((delta == 0.0) && (p1_evt != 0)) && ((( !(_x_p1_l3 != 0)) && (( !(_x_p1_l2 != 0)) && (( !(_x_p1_l0 != 0)) && ( !(_x_p1_l1 != 0))))) && (( !(p1_l3 != 0)) && (( !(p1_l2 != 0)) && ((p1_l1 != 0) && ( !(p1_l0 != 0)))))))))) && ((((v1 == 2) && ( !(p1_c <= max_prop))) && ( !(proposed1 <= _x_proposed1))) || ( !(((delta == 0.0) && (p1_evt != 0)) && ((( !(p1_l3 != 0)) && (( !(p1_l2 != 0)) && ((p1_l1 != 0) && ( !(p1_l0 != 0))))) && (( !(_x_p1_l3 != 0)) && (( !(_x_p1_l2 != 0)) && ((_x_p1_l0 != 0) && (_x_p1_l1 != 0))))))))) && (((((v2 != 0) == (_x_v2 != 0)) && (v1 == _x_v1)) && ((proposed1 == _x_proposed1) && ((( !(_x_p1_l3 != 0)) && (( !(_x_p1_l2 != 0)) && (( !(_x_p1_l0 != 0)) && ( !(_x_p1_l1 != 0))))) || (( !(_x_p1_l3 != 0)) && ((_x_p1_l2 != 0) && (( !(_x_p1_l0 != 0)) && ( !(_x_p1_l1 != 0)))))))) || ( !((( !(p1_l3 != 0)) && (( !(p1_l2 != 0)) && ((p1_l0 != 0) && (p1_l1 != 0)))) && ((delta == 0.0) && (p1_evt != 0)))))) && (((v2 != 0) && (p1_c == _x_p1_c)) || ( !(((delta == 0.0) && (p1_evt != 0)) && ((( !(_x_p1_l3 != 0)) && (( !(_x_p1_l2 != 0)) && (( !(_x_p1_l0 != 0)) && ( !(_x_p1_l1 != 0))))) && (( !(p1_l3 != 0)) && (( !(p1_l2 != 0)) && ((p1_l0 != 0) && (p1_l1 != 0))))))))) && ((( !(v2 != 0)) && (_x_p1_c == 0.0)) || ( !(((delta == 0.0) && (p1_evt != 0)) && ((( !(p1_l3 != 0)) && (( !(p1_l2 != 0)) && ((p1_l0 != 0) && (p1_l1 != 0)))) && (( !(_x_p1_l3 != 0)) && ((_x_p1_l2 != 0) && (( !(_x_p1_l0 != 0)) && ( !(_x_p1_l1 != 0)))))))))) && ((((v1 == _x_v1) && (proposed1 == _x_proposed1)) && ((_x_p1_c == 0.0) && ((_x_v2 != 0) && (( !(_x_p1_l3 != 0)) && ((_x_p1_l2 != 0) && ((_x_p1_l0 != 0) && ( !(_x_p1_l1 != 0)))))))) || ( !((( !(p1_l3 != 0)) && ((p1_l2 != 0) && (( !(p1_l0 != 0)) && ( !(p1_l1 != 0))))) && ((delta == 0.0) && (p1_evt != 0)))))) && (((proposed1 == _x_proposed1) && ((((v2 != 0) == (_x_v2 != 0)) && (v1 == _x_v1)) && ((p1_c == _x_p1_c) && ((( !(_x_p1_l3 != 0)) && (( !(_x_p1_l2 != 0)) && (( !(_x_p1_l0 != 0)) && ( !(_x_p1_l1 != 0))))) || (( !(_x_p1_l3 != 0)) && ((_x_p1_l2 != 0) && ((_x_p1_l1 != 0) && ( !(_x_p1_l0 != 0))))))))) || ( !((( !(p1_l3 != 0)) && ((p1_l2 != 0) && ((p1_l0 != 0) && ( !(p1_l1 != 0))))) && ((delta == 0.0) && (p1_evt != 0)))))) && (( !(v1 == 2)) || ( !(((delta == 0.0) && (p1_evt != 0)) && ((( !(_x_p1_l3 != 0)) && (( !(_x_p1_l2 != 0)) && (( !(_x_p1_l0 != 0)) && ( !(_x_p1_l1 != 0))))) && (( !(p1_l3 != 0)) && ((p1_l2 != 0) && ((p1_l0 != 0) && ( !(p1_l1 != 0)))))))))) && ((v1 == 2) || ( !(((delta == 0.0) && (p1_evt != 0)) && ((( !(p1_l3 != 0)) && ((p1_l2 != 0) && ((p1_l0 != 0) && ( !(p1_l1 != 0))))) && (( !(_x_p1_l3 != 0)) && ((_x_p1_l2 != 0) && ((_x_p1_l1 != 0) && ( !(_x_p1_l0 != 0)))))))))) && (((proposed1 == _x_proposed1) && ((((v2 != 0) == (_x_v2 != 0)) && (v1 == _x_v1)) && ((( !(_x_p1_l3 != 0)) && ((_x_p1_l2 != 0) && ((_x_p1_l0 != 0) && (_x_p1_l1 != 0)))) && (_x_p1_c == 0.0)))) || ( !((( !(p1_l3 != 0)) && ((p1_l2 != 0) && ((p1_l1 != 0) && ( !(p1_l0 != 0))))) && ((delta == 0.0) && (p1_evt != 0)))))) && (((proposed1 == _x_proposed1) && ((( !(_x_v2 != 0)) && ((_x_p1_l3 != 0) && (( !(_x_p1_l2 != 0)) && (( !(_x_p1_l0 != 0)) && ( !(_x_p1_l1 != 0)))))) && ((v1 == _x_v1) && (_x_p1_c == 0.0)))) || ( !((( !(p1_l3 != 0)) && ((p1_l2 != 0) && ((p1_l0 != 0) && (p1_l1 != 0)))) && ((delta == 0.0) && (p1_evt != 0)))))) && (((proposed1 == _x_proposed1) && (((_x_v1 == 0) && (( !(_x_p1_l3 != 0)) && (( !(_x_p1_l2 != 0)) && (( !(_x_p1_l0 != 0)) && ( !(_x_p1_l1 != 0)))))) && (((v2 != 0) == (_x_v2 != 0)) && (p1_c == _x_p1_c)))) || ( !(((p1_l3 != 0) && (( !(p1_l2 != 0)) && (( !(p1_l0 != 0)) && ( !(p1_l1 != 0))))) && ((delta == 0.0) && (p1_evt != 0)))))) && (((((((((((((((((((((_x_p0_l3 != 0) && (( !(_x_p0_l2 != 0)) && (( !(_x_p0_l0 != 0)) && ( !(_x_p0_l1 != 0))))) || ((( !(_x_p0_l3 != 0)) && ((_x_p0_l2 != 0) && ((_x_p0_l0 != 0) && (_x_p0_l1 != 0)))) || ((( !(_x_p0_l3 != 0)) && ((_x_p0_l2 != 0) && ((_x_p0_l1 != 0) && ( !(_x_p0_l0 != 0))))) || ((( !(_x_p0_l3 != 0)) && ((_x_p0_l2 != 0) && ((_x_p0_l0 != 0) && ( !(_x_p0_l1 != 0))))) || ((( !(_x_p0_l3 != 0)) && ((_x_p0_l2 != 0) && (( !(_x_p0_l0 != 0)) && ( !(_x_p0_l1 != 0))))) || ((( !(_x_p0_l3 != 0)) && (( !(_x_p0_l2 != 0)) && ((_x_p0_l0 != 0) && (_x_p0_l1 != 0)))) || ((( !(_x_p0_l3 != 0)) && (( !(_x_p0_l2 != 0)) && ((_x_p0_l1 != 0) && ( !(_x_p0_l0 != 0))))) || ((( !(_x_p0_l3 != 0)) && (( !(_x_p0_l2 != 0)) && (( !(_x_p0_l0 != 0)) && ( !(_x_p0_l1 != 0))))) || (( !(_x_p0_l3 != 0)) && (( !(_x_p0_l2 != 0)) && ((_x_p0_l0 != 0) && ( !(_x_p0_l1 != 0))))))))))))) && ((_x_p0_c <= _x_proposed0) || ( !(((( !(_x_p0_l3 != 0)) && (( !(_x_p0_l2 != 0)) && ((_x_p0_l0 != 0) && ( !(_x_p0_l1 != 0))))) || (( !(_x_p0_l3 != 0)) && ((_x_p0_l2 != 0) && (( !(_x_p0_l0 != 0)) && ( !(_x_p0_l1 != 0)))))) || ((( !(_x_p0_l3 != 0)) && ((_x_p0_l2 != 0) && ((_x_p0_l0 != 0) && (_x_p0_l1 != 0)))) || ((_x_p0_l3 != 0) && (( !(_x_p0_l2 != 0)) && (( !(_x_p0_l0 != 0)) && ( !(_x_p0_l1 != 0)))))))))) && ((((((((p0_l0 != 0) == (_x_p0_l0 != 0)) && ((p0_l1 != 0) == (_x_p0_l1 != 0))) && ((p0_l2 != 0) == (_x_p0_l2 != 0))) && ((p0_l3 != 0) == (_x_p0_l3 != 0))) && ((delta + (p0_c + (-1.0 * _x_p0_c))) == 0.0)) && (proposed0 == _x_proposed0)) || ( !(( !(p0_evt != 0)) || ( !(delta <= 0.0)))))) && (((((( !(_x_p0_l3 != 0)) && (( !(_x_p0_l2 != 0)) && ((_x_p0_l0 != 0) && ( !(_x_p0_l1 != 0))))) && (v1 == 0)) && ((_x_p0_c == 0.0) && ((v2 != 0) == (_x_v2 != 0)))) && ((proposed0 == _x_proposed0) && (v1 == _x_v1))) || ( !((( !(p0_l3 != 0)) && (( !(p0_l2 != 0)) && (( !(p0_l0 != 0)) && ( !(p0_l1 != 0))))) && ((p0_evt != 0) && (delta == 0.0)))))) && (((proposed0 == _x_proposed0) && (((_x_p0_c == 0.0) && ((v2 != 0) == (_x_v2 != 0))) && ((( !(_x_p0_l3 != 0)) && (( !(_x_p0_l2 != 0)) && ((_x_p0_l1 != 0) && ( !(_x_p0_l0 != 0))))) && (_x_v1 == 1)))) || ( !((( !(p0_l3 != 0)) && (( !(p0_l2 != 0)) && ((p0_l0 != 0) && ( !(p0_l1 != 0))))) && ((p0_evt != 0) && (delta == 0.0)))))) && (((((( !(_x_p0_l3 != 0)) && (( !(_x_p0_l2 != 0)) && (( !(_x_p0_l0 != 0)) && ( !(_x_p0_l1 != 0))))) || (( !(_x_p0_l3 != 0)) && (( !(_x_p0_l2 != 0)) && ((_x_p0_l0 != 0) && (_x_p0_l1 != 0))))) && (p0_c == _x_p0_c)) && (((v2 != 0) == (_x_v2 != 0)) && (v1 == _x_v1))) || ( !((( !(p0_l3 != 0)) && (( !(p0_l2 != 0)) && ((p0_l1 != 0) && ( !(p0_l0 != 0))))) && ((p0_evt != 0) && (delta == 0.0)))))) && (((proposed0 == _x_proposed0) && ( !(v1 == 1))) || ( !(((p0_evt != 0) && (delta == 0.0)) && ((( !(_x_p0_l3 != 0)) && (( !(_x_p0_l2 != 0)) && (( !(_x_p0_l0 != 0)) && ( !(_x_p0_l1 != 0))))) && (( !(p0_l3 != 0)) && (( !(p0_l2 != 0)) && ((p0_l1 != 0) && ( !(p0_l0 != 0)))))))))) && ((((v1 == 1) && ( !(p0_c <= max_prop))) && ( !(proposed0 <= _x_proposed0))) || ( !(((p0_evt != 0) && (delta == 0.0)) && ((( !(p0_l3 != 0)) && (( !(p0_l2 != 0)) && ((p0_l1 != 0) && ( !(p0_l0 != 0))))) && (( !(_x_p0_l3 != 0)) && (( !(_x_p0_l2 != 0)) && ((_x_p0_l0 != 0) && (_x_p0_l1 != 0))))))))) && (((((v2 != 0) == (_x_v2 != 0)) && (v1 == _x_v1)) && ((proposed0 == _x_proposed0) && ((( !(_x_p0_l3 != 0)) && (( !(_x_p0_l2 != 0)) && (( !(_x_p0_l0 != 0)) && ( !(_x_p0_l1 != 0))))) || (( !(_x_p0_l3 != 0)) && ((_x_p0_l2 != 0) && (( !(_x_p0_l0 != 0)) && ( !(_x_p0_l1 != 0)))))))) || ( !((( !(p0_l3 != 0)) && (( !(p0_l2 != 0)) && ((p0_l0 != 0) && (p0_l1 != 0)))) && ((p0_evt != 0) && (delta == 0.0)))))) && (((v2 != 0) && (p0_c == _x_p0_c)) || ( !(((p0_evt != 0) && (delta == 0.0)) && ((( !(_x_p0_l3 != 0)) && (( !(_x_p0_l2 != 0)) && (( !(_x_p0_l0 != 0)) && ( !(_x_p0_l1 != 0))))) && (( !(p0_l3 != 0)) && (( !(p0_l2 != 0)) && ((p0_l0 != 0) && (p0_l1 != 0))))))))) && (((_x_p0_c == 0.0) && ( !(v2 != 0))) || ( !(((p0_evt != 0) && (delta == 0.0)) && ((( !(p0_l3 != 0)) && (( !(p0_l2 != 0)) && ((p0_l0 != 0) && (p0_l1 != 0)))) && (( !(_x_p0_l3 != 0)) && ((_x_p0_l2 != 0) && (( !(_x_p0_l0 != 0)) && ( !(_x_p0_l1 != 0)))))))))) && ((((proposed0 == _x_proposed0) && (v1 == _x_v1)) && ((_x_p0_c == 0.0) && ((_x_v2 != 0) && (( !(_x_p0_l3 != 0)) && ((_x_p0_l2 != 0) && ((_x_p0_l0 != 0) && ( !(_x_p0_l1 != 0)))))))) || ( !((( !(p0_l3 != 0)) && ((p0_l2 != 0) && (( !(p0_l0 != 0)) && ( !(p0_l1 != 0))))) && ((p0_evt != 0) && (delta == 0.0)))))) && (((proposed0 == _x_proposed0) && ((((v2 != 0) == (_x_v2 != 0)) && (v1 == _x_v1)) && ((p0_c == _x_p0_c) && ((( !(_x_p0_l3 != 0)) && (( !(_x_p0_l2 != 0)) && (( !(_x_p0_l0 != 0)) && ( !(_x_p0_l1 != 0))))) || (( !(_x_p0_l3 != 0)) && ((_x_p0_l2 != 0) && ((_x_p0_l1 != 0) && ( !(_x_p0_l0 != 0))))))))) || ( !((( !(p0_l3 != 0)) && ((p0_l2 != 0) && ((p0_l0 != 0) && ( !(p0_l1 != 0))))) && ((p0_evt != 0) && (delta == 0.0)))))) && (( !(v1 == 1)) || ( !(((p0_evt != 0) && (delta == 0.0)) && ((( !(_x_p0_l3 != 0)) && (( !(_x_p0_l2 != 0)) && (( !(_x_p0_l0 != 0)) && ( !(_x_p0_l1 != 0))))) && (( !(p0_l3 != 0)) && ((p0_l2 != 0) && ((p0_l0 != 0) && ( !(p0_l1 != 0)))))))))) && ((v1 == 1) || ( !(((p0_evt != 0) && (delta == 0.0)) && ((( !(p0_l3 != 0)) && ((p0_l2 != 0) && ((p0_l0 != 0) && ( !(p0_l1 != 0))))) && (( !(_x_p0_l3 != 0)) && ((_x_p0_l2 != 0) && ((_x_p0_l1 != 0) && ( !(_x_p0_l0 != 0)))))))))) && (((proposed0 == _x_proposed0) && ((((v2 != 0) == (_x_v2 != 0)) && (v1 == _x_v1)) && ((( !(_x_p0_l3 != 0)) && ((_x_p0_l2 != 0) && ((_x_p0_l0 != 0) && (_x_p0_l1 != 0)))) && (_x_p0_c == 0.0)))) || ( !((( !(p0_l3 != 0)) && ((p0_l2 != 0) && ((p0_l1 != 0) && ( !(p0_l0 != 0))))) && ((p0_evt != 0) && (delta == 0.0)))))) && (((proposed0 == _x_proposed0) && ((((_x_p0_l3 != 0) && (( !(_x_p0_l2 != 0)) && (( !(_x_p0_l0 != 0)) && ( !(_x_p0_l1 != 0))))) && ( !(_x_v2 != 0))) && ((_x_p0_c == 0.0) && (v1 == _x_v1)))) || ( !((( !(p0_l3 != 0)) && ((p0_l2 != 0) && ((p0_l0 != 0) && (p0_l1 != 0)))) && ((p0_evt != 0) && (delta == 0.0)))))) && (((proposed0 == _x_proposed0) && (((( !(_x_p0_l3 != 0)) && (( !(_x_p0_l2 != 0)) && (( !(_x_p0_l0 != 0)) && ( !(_x_p0_l1 != 0))))) && (_x_v1 == 0)) && (((v2 != 0) == (_x_v2 != 0)) && (p0_c == _x_p0_c)))) || ( !(((p0_l3 != 0) && (( !(p0_l2 != 0)) && (( !(p0_l0 != 0)) && ( !(p0_l1 != 0))))) && ((p0_evt != 0) && (delta == 0.0)))))) && ((((((((_x_v1 == 4) || ((_x_v1 == 3) || ((_x_v1 == 2) || ((_x_v1 == 1) || (_x_v1 == 0))))) && (0.0 <= _x_delta)) && (( !(_x_proposed0 <= 0.0)) && (_x_proposed0 <= _x_max_prop))) && (( !(_x_proposed1 <= 0.0)) && (_x_proposed1 <= _x_max_prop))) && (( !(_x_proposed2 <= 0.0)) && (_x_proposed2 <= _x_max_prop))) && (( !(_x_proposed3 <= 0.0)) && (_x_proposed3 <= _x_max_prop))) && ((((_x_max_prop == _x_proposed0) || (_x_max_prop == _x_proposed1)) || (_x_max_prop == _x_proposed2)) || (_x_max_prop == _x_proposed3))))))) && ((delta <= 0.0) || (((v2 != 0) == (_x_v2 != 0)) && (v1 == _x_v1)))) && (( !(( !(p3_evt != 0)) && (( !(p2_evt != 0)) && (( !(p0_evt != 0)) && ( !(p1_evt != 0)))))) || ( !(delta == 0.0)))) && ((_x_inc_max_prop != 0) == (max_prop <= _x_max_prop))) && (((delta == _x__diverge_delta) || ( !(1.0 <= _diverge_delta))) && ((1.0 <= _diverge_delta) || ((delta + (_diverge_delta + (-1.0 * _x__diverge_delta))) == 0.0))));
    _diverge_delta = _x__diverge_delta;
    p3_l1 = _x_p3_l1;
    p3_l0 = _x_p3_l0;
    p3_l3 = _x_p3_l3;
    p0_evt = _x_p0_evt;
    p0_l0 = _x_p0_l0;
    p3_l2 = _x_p3_l2;
    p0_c = _x_p0_c;
    proposed1 = _x_proposed1;
    p1_l3 = _x_p1_l3;
    proposed0 = _x_proposed0;
    p1_l2 = _x_p1_l2;
    inc_max_prop = _x_inc_max_prop;
    p1_evt = _x_p1_evt;
    p1_l1 = _x_p1_l1;
    p2_l3 = _x_p2_l3;
    max_prop = _x_max_prop;
    p1_c = _x_p1_c;
    p1_l0 = _x_p1_l0;
    p2_l2 = _x_p2_l2;
    v2 = _x_v2;
    p2_l1 = _x_p2_l1;
    v1 = _x_v1;
    p0_l1 = _x_p0_l1;
    p2_c = _x_p2_c;
    p2_l0 = _x_p2_l0;
    delta = _x_delta;
    proposed3 = _x_proposed3;
    p3_evt = _x_p3_evt;
    p2_evt = _x_p2_evt;
    p0_l2 = _x_p0_l2;
    p0_l3 = _x_p0_l3;
    proposed2 = _x_proposed2;
    p3_c = _x_p3_c;

  }
}
