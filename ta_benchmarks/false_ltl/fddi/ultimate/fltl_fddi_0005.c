//@ ltl invariant negative: ( ([] (<> ( AP((s0_l2 != 0)) && ( AP((s0_l0 != 0)) && (! AP((s0_l1 != 0))))))) || (! ([] (<> AP((1.0 <= _diverge_delta))))));

extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);

char __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}


float _diverge_delta, _x__diverge_delta;
char s4_l2, _x_s4_l2;
char s4_evt1, _x_s4_evt1;
float s4_z, _x_s4_z;
char s3_l2, _x_s3_l2;
char s3_l1, _x_s3_l1;
char s3_l0, _x_s3_l0;
char s3_evt1, _x_s3_evt1;
char s3_evt0, _x_s3_evt0;
float s3_y, _x_s3_y;
float s3_x, _x_s3_x;
char s2_l2, _x_s2_l2;
char s2_l1, _x_s2_l1;
char s0_l0, _x_s0_l0;
char s2_l0, _x_s2_l0;
char s2_evt1, _x_s2_evt1;
char s2_evt0, _x_s2_evt0;
float s0_z, _x_s0_z;
float s3_z, _x_s3_z;
char r_l, _x_r_l;
float s2_z, _x_s2_z;
float s0_y, _x_s0_y;
float s2_y, _x_s2_y;
float s0_x, _x_s0_x;
float s2_x, _x_s2_x;
float s4_y, _x_s4_y;
float s1_z, _x_s1_z;
char s1_l0, _x_s1_l0;
int r_evt_id, _x_r_evt_id;
float delta, _x_delta;
float s4_x, _x_s4_x;
float s1_y, _x_s1_y;
char s0_l1, _x_s0_l1;
char s0_l2, _x_s0_l2;
float s1_x, _x_s1_x;
char r_event0, _x_r_event0;
char s1_evt0, _x_s1_evt0;
char s4_evt0, _x_s4_evt0;
char r_event1, _x_r_event1;
char s1_evt1, _x_s1_evt1;
char s4_l0, _x_s4_l0;
char s0_evt0, _x_s0_evt0;
int r_counter, _x_r_counter;
char s1_l1, _x_s1_l1;
char s4_l1, _x_s4_l1;
char s0_evt1, _x_s0_evt1;
float r_x, _x_r_x;
char s1_l2, _x_s1_l2;

int main()
{
  _diverge_delta = __VERIFIER_nondet_float();
  s4_l2 = __VERIFIER_nondet_bool();
  s4_evt1 = __VERIFIER_nondet_bool();
  s4_z = __VERIFIER_nondet_float();
  s3_l2 = __VERIFIER_nondet_bool();
  s3_l1 = __VERIFIER_nondet_bool();
  s3_l0 = __VERIFIER_nondet_bool();
  s3_evt1 = __VERIFIER_nondet_bool();
  s3_evt0 = __VERIFIER_nondet_bool();
  s3_y = __VERIFIER_nondet_float();
  s3_x = __VERIFIER_nondet_float();
  s2_l2 = __VERIFIER_nondet_bool();
  s2_l1 = __VERIFIER_nondet_bool();
  s0_l0 = __VERIFIER_nondet_bool();
  s2_l0 = __VERIFIER_nondet_bool();
  s2_evt1 = __VERIFIER_nondet_bool();
  s2_evt0 = __VERIFIER_nondet_bool();
  s0_z = __VERIFIER_nondet_float();
  s3_z = __VERIFIER_nondet_float();
  r_l = __VERIFIER_nondet_bool();
  s2_z = __VERIFIER_nondet_float();
  s0_y = __VERIFIER_nondet_float();
  s2_y = __VERIFIER_nondet_float();
  s0_x = __VERIFIER_nondet_float();
  s2_x = __VERIFIER_nondet_float();
  s4_y = __VERIFIER_nondet_float();
  s1_z = __VERIFIER_nondet_float();
  s1_l0 = __VERIFIER_nondet_bool();
  r_evt_id = __VERIFIER_nondet_int();
  delta = __VERIFIER_nondet_float();
  s4_x = __VERIFIER_nondet_float();
  s1_y = __VERIFIER_nondet_float();
  s0_l1 = __VERIFIER_nondet_bool();
  s0_l2 = __VERIFIER_nondet_bool();
  s1_x = __VERIFIER_nondet_float();
  r_event0 = __VERIFIER_nondet_bool();
  s1_evt0 = __VERIFIER_nondet_bool();
  s4_evt0 = __VERIFIER_nondet_bool();
  r_event1 = __VERIFIER_nondet_bool();
  s1_evt1 = __VERIFIER_nondet_bool();
  s4_l0 = __VERIFIER_nondet_bool();
  s0_evt0 = __VERIFIER_nondet_bool();
  r_counter = __VERIFIER_nondet_int();
  s1_l1 = __VERIFIER_nondet_bool();
  s4_l1 = __VERIFIER_nondet_bool();
  s0_evt1 = __VERIFIER_nondet_bool();
  r_x = __VERIFIER_nondet_float();
  s1_l2 = __VERIFIER_nondet_bool();

  int __ok = ((((((((((( !(s4_evt0 != 0)) && ( !(s4_evt1 != 0))) || ((s4_evt0 != 0) && ( !(s4_evt1 != 0)))) || (((s4_evt1 != 0) && ( !(s4_evt0 != 0))) || ((s4_evt0 != 0) && (s4_evt1 != 0)))) && ((((( !(s4_l2 != 0)) && (( !(s4_l0 != 0)) && ( !(s4_l1 != 0)))) || (( !(s4_l2 != 0)) && ((s4_l0 != 0) && ( !(s4_l1 != 0))))) || ((( !(s4_l2 != 0)) && ((s4_l1 != 0) && ( !(s4_l0 != 0)))) || (( !(s4_l2 != 0)) && ((s4_l0 != 0) && (s4_l1 != 0))))) || (((s4_l2 != 0) && (( !(s4_l0 != 0)) && ( !(s4_l1 != 0)))) || ((s4_l2 != 0) && ((s4_l0 != 0) && ( !(s4_l1 != 0))))))) && (((( !(s4_l2 != 0)) && (( !(s4_l0 != 0)) && ( !(s4_l1 != 0)))) && (s4_x == 0.0)) && ((s4_y == 0.0) && (s4_z == 0.0)))) && ((s4_x <= 20.0) || ( !(( !(s4_l2 != 0)) && ((s4_l0 != 0) && ( !(s4_l1 != 0))))))) && ((s4_x <= 120.0) || ( !(( !(s4_l2 != 0)) && ((s4_l1 != 0) && ( !(s4_l0 != 0))))))) && ((s4_x <= 120.0) || ( !((s4_l2 != 0) && ((s4_l0 != 0) && ( !(s4_l1 != 0))))))) && (((((((((( !(s3_evt0 != 0)) && ( !(s3_evt1 != 0))) || ((s3_evt0 != 0) && ( !(s3_evt1 != 0)))) || (((s3_evt1 != 0) && ( !(s3_evt0 != 0))) || ((s3_evt0 != 0) && (s3_evt1 != 0)))) && ((((( !(s3_l2 != 0)) && (( !(s3_l0 != 0)) && ( !(s3_l1 != 0)))) || (( !(s3_l2 != 0)) && ((s3_l0 != 0) && ( !(s3_l1 != 0))))) || ((( !(s3_l2 != 0)) && ((s3_l1 != 0) && ( !(s3_l0 != 0)))) || (( !(s3_l2 != 0)) && ((s3_l0 != 0) && (s3_l1 != 0))))) || (((s3_l2 != 0) && (( !(s3_l0 != 0)) && ( !(s3_l1 != 0)))) || ((s3_l2 != 0) && ((s3_l0 != 0) && ( !(s3_l1 != 0))))))) && (((( !(s3_l2 != 0)) && (( !(s3_l0 != 0)) && ( !(s3_l1 != 0)))) && (s3_x == 0.0)) && ((s3_y == 0.0) && (s3_z == 0.0)))) && ((s3_x <= 20.0) || ( !(( !(s3_l2 != 0)) && ((s3_l0 != 0) && ( !(s3_l1 != 0))))))) && ((s3_x <= 120.0) || ( !(( !(s3_l2 != 0)) && ((s3_l1 != 0) && ( !(s3_l0 != 0))))))) && ((s3_x <= 120.0) || ( !((s3_l2 != 0) && ((s3_l0 != 0) && ( !(s3_l1 != 0))))))) && (((((((((( !(s2_evt0 != 0)) && ( !(s2_evt1 != 0))) || ((s2_evt0 != 0) && ( !(s2_evt1 != 0)))) || (((s2_evt1 != 0) && ( !(s2_evt0 != 0))) || ((s2_evt0 != 0) && (s2_evt1 != 0)))) && ((((( !(s2_l2 != 0)) && (( !(s2_l0 != 0)) && ( !(s2_l1 != 0)))) || (( !(s2_l2 != 0)) && ((s2_l0 != 0) && ( !(s2_l1 != 0))))) || ((( !(s2_l2 != 0)) && ((s2_l1 != 0) && ( !(s2_l0 != 0)))) || (( !(s2_l2 != 0)) && ((s2_l0 != 0) && (s2_l1 != 0))))) || (((s2_l2 != 0) && (( !(s2_l0 != 0)) && ( !(s2_l1 != 0)))) || ((s2_l2 != 0) && ((s2_l0 != 0) && ( !(s2_l1 != 0))))))) && (((( !(s2_l2 != 0)) && (( !(s2_l0 != 0)) && ( !(s2_l1 != 0)))) && (s2_x == 0.0)) && ((s2_y == 0.0) && (s2_z == 0.0)))) && ((s2_x <= 20.0) || ( !(( !(s2_l2 != 0)) && ((s2_l0 != 0) && ( !(s2_l1 != 0))))))) && ((s2_x <= 120.0) || ( !(( !(s2_l2 != 0)) && ((s2_l1 != 0) && ( !(s2_l0 != 0))))))) && ((s2_x <= 120.0) || ( !((s2_l2 != 0) && ((s2_l0 != 0) && ( !(s2_l1 != 0))))))) && (((((((((( !(s1_evt0 != 0)) && ( !(s1_evt1 != 0))) || ((s1_evt0 != 0) && ( !(s1_evt1 != 0)))) || (((s1_evt1 != 0) && ( !(s1_evt0 != 0))) || ((s1_evt0 != 0) && (s1_evt1 != 0)))) && ((((( !(s1_l2 != 0)) && (( !(s1_l0 != 0)) && ( !(s1_l1 != 0)))) || (( !(s1_l2 != 0)) && ((s1_l0 != 0) && ( !(s1_l1 != 0))))) || ((( !(s1_l2 != 0)) && ((s1_l1 != 0) && ( !(s1_l0 != 0)))) || (( !(s1_l2 != 0)) && ((s1_l0 != 0) && (s1_l1 != 0))))) || (((s1_l2 != 0) && (( !(s1_l0 != 0)) && ( !(s1_l1 != 0)))) || ((s1_l2 != 0) && ((s1_l0 != 0) && ( !(s1_l1 != 0))))))) && (((( !(s1_l2 != 0)) && (( !(s1_l0 != 0)) && ( !(s1_l1 != 0)))) && (s1_x == 0.0)) && ((s1_y == 0.0) && (s1_z == 0.0)))) && ((s1_x <= 20.0) || ( !(( !(s1_l2 != 0)) && ((s1_l0 != 0) && ( !(s1_l1 != 0))))))) && ((s1_x <= 120.0) || ( !(( !(s1_l2 != 0)) && ((s1_l1 != 0) && ( !(s1_l0 != 0))))))) && ((s1_x <= 120.0) || ( !((s1_l2 != 0) && ((s1_l0 != 0) && ( !(s1_l1 != 0))))))) && (((((((((( !(s0_evt0 != 0)) && ( !(s0_evt1 != 0))) || ((s0_evt0 != 0) && ( !(s0_evt1 != 0)))) || (((s0_evt1 != 0) && ( !(s0_evt0 != 0))) || ((s0_evt0 != 0) && (s0_evt1 != 0)))) && ((((( !(s0_l2 != 0)) && (( !(s0_l0 != 0)) && ( !(s0_l1 != 0)))) || (( !(s0_l2 != 0)) && ((s0_l0 != 0) && ( !(s0_l1 != 0))))) || ((( !(s0_l2 != 0)) && ((s0_l1 != 0) && ( !(s0_l0 != 0)))) || (( !(s0_l2 != 0)) && ((s0_l0 != 0) && (s0_l1 != 0))))) || (((s0_l2 != 0) && (( !(s0_l0 != 0)) && ( !(s0_l1 != 0)))) || ((s0_l2 != 0) && ((s0_l0 != 0) && ( !(s0_l1 != 0))))))) && (((( !(s0_l2 != 0)) && (( !(s0_l0 != 0)) && ( !(s0_l1 != 0)))) && (s0_x == 0.0)) && ((s0_y == 0.0) && (s0_z == 0.0)))) && ((s0_x <= 20.0) || ( !(( !(s0_l2 != 0)) && ((s0_l0 != 0) && ( !(s0_l1 != 0))))))) && ((s0_x <= 120.0) || ( !(( !(s0_l2 != 0)) && ((s0_l1 != 0) && ( !(s0_l0 != 0))))))) && ((s0_x <= 120.0) || ( !((s0_l2 != 0) && ((s0_l0 != 0) && ( !(s0_l1 != 0))))))) && (((((((r_l != 0) && ((r_counter == 0) && (r_x == 0.0))) && ((( !(r_event0 != 0)) && ( !(r_event1 != 0))) || (((r_event0 != 0) && ( !(r_event1 != 0))) || ((r_event1 != 0) && ( !(r_event0 != 0)))))) && (((((r_evt_id == 0) || (r_evt_id == 1)) || (r_evt_id == 2)) || (r_evt_id == 3)) || (r_evt_id == 4))) && (((((r_counter == 0) || (r_counter == 1)) || (r_counter == 2)) || (r_counter == 3)) || (r_counter == 4))) && (( !(r_l != 0)) || (r_x <= 0.0))) && (0.0 <= delta))))))) && (delta == _diverge_delta));
  while (__ok) {
    _x__diverge_delta = __VERIFIER_nondet_float();
    _x_s4_l2 = __VERIFIER_nondet_bool();
    _x_s4_evt1 = __VERIFIER_nondet_bool();
    _x_s4_z = __VERIFIER_nondet_float();
    _x_s3_l2 = __VERIFIER_nondet_bool();
    _x_s3_l1 = __VERIFIER_nondet_bool();
    _x_s3_l0 = __VERIFIER_nondet_bool();
    _x_s3_evt1 = __VERIFIER_nondet_bool();
    _x_s3_evt0 = __VERIFIER_nondet_bool();
    _x_s3_y = __VERIFIER_nondet_float();
    _x_s3_x = __VERIFIER_nondet_float();
    _x_s2_l2 = __VERIFIER_nondet_bool();
    _x_s2_l1 = __VERIFIER_nondet_bool();
    _x_s0_l0 = __VERIFIER_nondet_bool();
    _x_s2_l0 = __VERIFIER_nondet_bool();
    _x_s2_evt1 = __VERIFIER_nondet_bool();
    _x_s2_evt0 = __VERIFIER_nondet_bool();
    _x_s0_z = __VERIFIER_nondet_float();
    _x_s3_z = __VERIFIER_nondet_float();
    _x_r_l = __VERIFIER_nondet_bool();
    _x_s2_z = __VERIFIER_nondet_float();
    _x_s0_y = __VERIFIER_nondet_float();
    _x_s2_y = __VERIFIER_nondet_float();
    _x_s0_x = __VERIFIER_nondet_float();
    _x_s2_x = __VERIFIER_nondet_float();
    _x_s4_y = __VERIFIER_nondet_float();
    _x_s1_z = __VERIFIER_nondet_float();
    _x_s1_l0 = __VERIFIER_nondet_bool();
    _x_r_evt_id = __VERIFIER_nondet_int();
    _x_delta = __VERIFIER_nondet_float();
    _x_s4_x = __VERIFIER_nondet_float();
    _x_s1_y = __VERIFIER_nondet_float();
    _x_s0_l1 = __VERIFIER_nondet_bool();
    _x_s0_l2 = __VERIFIER_nondet_bool();
    _x_s1_x = __VERIFIER_nondet_float();
    _x_r_event0 = __VERIFIER_nondet_bool();
    _x_s1_evt0 = __VERIFIER_nondet_bool();
    _x_s4_evt0 = __VERIFIER_nondet_bool();
    _x_r_event1 = __VERIFIER_nondet_bool();
    _x_s1_evt1 = __VERIFIER_nondet_bool();
    _x_s4_l0 = __VERIFIER_nondet_bool();
    _x_s0_evt0 = __VERIFIER_nondet_bool();
    _x_r_counter = __VERIFIER_nondet_int();
    _x_s1_l1 = __VERIFIER_nondet_bool();
    _x_s4_l1 = __VERIFIER_nondet_bool();
    _x_s0_evt1 = __VERIFIER_nondet_bool();
    _x_r_x = __VERIFIER_nondet_float();
    _x_s1_l2 = __VERIFIER_nondet_bool();

    __ok = ((((((((((((((((((((((((((((((((( !(_x_s4_evt0 != 0)) && ( !(_x_s4_evt1 != 0))) || ((_x_s4_evt0 != 0) && ( !(_x_s4_evt1 != 0)))) || (((_x_s4_evt1 != 0) && ( !(_x_s4_evt0 != 0))) || ((_x_s4_evt0 != 0) && (_x_s4_evt1 != 0)))) && ((((( !(_x_s4_l2 != 0)) && (( !(_x_s4_l0 != 0)) && ( !(_x_s4_l1 != 0)))) || (( !(_x_s4_l2 != 0)) && ((_x_s4_l0 != 0) && ( !(_x_s4_l1 != 0))))) || ((( !(_x_s4_l2 != 0)) && ((_x_s4_l1 != 0) && ( !(_x_s4_l0 != 0)))) || (( !(_x_s4_l2 != 0)) && ((_x_s4_l0 != 0) && (_x_s4_l1 != 0))))) || (((_x_s4_l2 != 0) && (( !(_x_s4_l0 != 0)) && ( !(_x_s4_l1 != 0)))) || ((_x_s4_l2 != 0) && ((_x_s4_l0 != 0) && ( !(_x_s4_l1 != 0))))))) && ((_x_s4_x <= 20.0) || ( !(( !(_x_s4_l2 != 0)) && ((_x_s4_l0 != 0) && ( !(_x_s4_l1 != 0))))))) && ((_x_s4_x <= 120.0) || ( !(( !(_x_s4_l2 != 0)) && ((_x_s4_l1 != 0) && ( !(_x_s4_l0 != 0))))))) && ((_x_s4_x <= 120.0) || ( !((_x_s4_l2 != 0) && ((_x_s4_l0 != 0) && ( !(_x_s4_l1 != 0))))))) && ((delta <= 0.0) || ((((delta + (s4_x + (-1.0 * _x_s4_x))) == 0.0) && ((delta + (s4_y + (-1.0 * _x_s4_y))) == 0.0)) && (((((s4_l0 != 0) == (_x_s4_l0 != 0)) && ((s4_l1 != 0) == (_x_s4_l1 != 0))) && ((s4_l2 != 0) == (_x_s4_l2 != 0))) && ((delta + (s4_z + (-1.0 * _x_s4_z))) == 0.0))))) && (((((((s4_l0 != 0) == (_x_s4_l0 != 0)) && ((s4_l1 != 0) == (_x_s4_l1 != 0))) && ((s4_l2 != 0) == (_x_s4_l2 != 0))) && ((delta + (s4_x + (-1.0 * _x_s4_x))) == 0.0)) && (((delta + (s4_y + (-1.0 * _x_s4_y))) == 0.0) && ((delta + (s4_z + (-1.0 * _x_s4_z))) == 0.0))) || ( !(( !(s4_evt0 != 0)) && ( !(s4_evt1 != 0)))))) && ((((((s4_evt0 != 0) && (s4_evt1 != 0)) && (( !(_x_s4_l2 != 0)) && ((_x_s4_l0 != 0) && ( !(_x_s4_l1 != 0))))) && ((_x_s4_x == 0.0) && (_x_s4_y == 0.0))) && (s4_z == _x_s4_z)) || ( !((( !(s4_l2 != 0)) && (( !(s4_l0 != 0)) && ( !(s4_l1 != 0)))) && ((delta == 0.0) && ( !(( !(s4_evt0 != 0)) && ( !(s4_evt1 != 0))))))))) && (((((( !(_x_s4_l2 != 0)) && ((_x_s4_l1 != 0) && ( !(_x_s4_l0 != 0)))) || (( !(_x_s4_l2 != 0)) && ((_x_s4_l0 != 0) && (_x_s4_l1 != 0)))) && (s4_x == _x_s4_x)) && ((s4_z == _x_s4_z) && (s4_y == _x_s4_y))) || ( !((( !(s4_l2 != 0)) && ((s4_l0 != 0) && ( !(s4_l1 != 0)))) && ((delta == 0.0) && ( !(( !(s4_evt0 != 0)) && ( !(s4_evt1 != 0))))))))) && ((((s4_evt0 != 0) && ( !(s4_evt1 != 0))) && ((20.0 <= s4_x) && ( !(120.0 <= s4_z)))) || ( !(((delta == 0.0) && ( !(( !(s4_evt0 != 0)) && ( !(s4_evt1 != 0))))) && ((( !(s4_l2 != 0)) && ((s4_l0 != 0) && ( !(s4_l1 != 0)))) && (( !(_x_s4_l2 != 0)) && ((_x_s4_l1 != 0) && ( !(_x_s4_l0 != 0))))))))) && ((((s4_evt1 != 0) && ( !(s4_evt0 != 0))) && ((20.0 <= s4_x) && (120.0 <= s4_z))) || ( !(((delta == 0.0) && ( !(( !(s4_evt0 != 0)) && ( !(s4_evt1 != 0))))) && ((( !(s4_l2 != 0)) && ((s4_l0 != 0) && ( !(s4_l1 != 0)))) && (( !(_x_s4_l2 != 0)) && ((_x_s4_l0 != 0) && (_x_s4_l1 != 0)))))))) && (((s4_z == _x_s4_z) && ((((s4_evt1 != 0) && ( !(s4_evt0 != 0))) && (( !(_x_s4_l2 != 0)) && ((_x_s4_l0 != 0) && (_x_s4_l1 != 0)))) && ((s4_x == _x_s4_x) && (s4_y == _x_s4_y)))) || ( !((( !(s4_l2 != 0)) && ((s4_l1 != 0) && ( !(s4_l0 != 0)))) && ((delta == 0.0) && ( !(( !(s4_evt0 != 0)) && ( !(s4_evt1 != 0))))))))) && ((((((s4_evt0 != 0) && (s4_evt1 != 0)) && ((_x_s4_l2 != 0) && (( !(_x_s4_l0 != 0)) && ( !(_x_s4_l1 != 0))))) && ((_x_s4_x == 0.0) && (s4_y == _x_s4_y))) && (_x_s4_z == 0.0)) || ( !((( !(s4_l2 != 0)) && ((s4_l0 != 0) && (s4_l1 != 0))) && ((delta == 0.0) && ( !(( !(s4_evt0 != 0)) && ( !(s4_evt1 != 0))))))))) && ((((s4_x == _x_s4_x) && (s4_y == _x_s4_y)) && ((s4_z == _x_s4_z) && ((( !(_x_s4_l2 != 0)) && (( !(_x_s4_l0 != 0)) && ( !(_x_s4_l1 != 0)))) || ((_x_s4_l2 != 0) && ((_x_s4_l0 != 0) && ( !(_x_s4_l1 != 0))))))) || ( !(((s4_l2 != 0) && (( !(s4_l0 != 0)) && ( !(s4_l1 != 0)))) && ((delta == 0.0) && ( !(( !(s4_evt0 != 0)) && ( !(s4_evt1 != 0))))))))) && ((((s4_evt0 != 0) && ( !(s4_evt1 != 0))) && ((20.0 <= s4_x) && ( !(120.0 <= s4_y)))) || ( !(((delta == 0.0) && ( !(( !(s4_evt0 != 0)) && ( !(s4_evt1 != 0))))) && (((s4_l2 != 0) && (( !(s4_l0 != 0)) && ( !(s4_l1 != 0)))) && ((_x_s4_l2 != 0) && ((_x_s4_l0 != 0) && ( !(_x_s4_l1 != 0))))))))) && ((((s4_evt1 != 0) && ( !(s4_evt0 != 0))) && ((20.0 <= s4_x) && (120.0 <= s4_y))) || ( !(((delta == 0.0) && ( !(( !(s4_evt0 != 0)) && ( !(s4_evt1 != 0))))) && ((( !(_x_s4_l2 != 0)) && (( !(_x_s4_l0 != 0)) && ( !(_x_s4_l1 != 0)))) && ((s4_l2 != 0) && (( !(s4_l0 != 0)) && ( !(s4_l1 != 0))))))))) && (((s4_z == _x_s4_z) && (((s4_x == _x_s4_x) && (s4_y == _x_s4_y)) && (((s4_evt1 != 0) && ( !(s4_evt0 != 0))) && (( !(_x_s4_l2 != 0)) && (( !(_x_s4_l0 != 0)) && ( !(_x_s4_l1 != 0))))))) || ( !(((s4_l2 != 0) && ((s4_l0 != 0) && ( !(s4_l1 != 0)))) && ((delta == 0.0) && ( !(( !(s4_evt0 != 0)) && ( !(s4_evt1 != 0))))))))) && ((((((((((((((((((((( !(_x_s3_evt0 != 0)) && ( !(_x_s3_evt1 != 0))) || ((_x_s3_evt0 != 0) && ( !(_x_s3_evt1 != 0)))) || (((_x_s3_evt1 != 0) && ( !(_x_s3_evt0 != 0))) || ((_x_s3_evt0 != 0) && (_x_s3_evt1 != 0)))) && ((((( !(_x_s3_l2 != 0)) && (( !(_x_s3_l0 != 0)) && ( !(_x_s3_l1 != 0)))) || (( !(_x_s3_l2 != 0)) && ((_x_s3_l0 != 0) && ( !(_x_s3_l1 != 0))))) || ((( !(_x_s3_l2 != 0)) && ((_x_s3_l1 != 0) && ( !(_x_s3_l0 != 0)))) || (( !(_x_s3_l2 != 0)) && ((_x_s3_l0 != 0) && (_x_s3_l1 != 0))))) || (((_x_s3_l2 != 0) && (( !(_x_s3_l0 != 0)) && ( !(_x_s3_l1 != 0)))) || ((_x_s3_l2 != 0) && ((_x_s3_l0 != 0) && ( !(_x_s3_l1 != 0))))))) && ((_x_s3_x <= 20.0) || ( !(( !(_x_s3_l2 != 0)) && ((_x_s3_l0 != 0) && ( !(_x_s3_l1 != 0))))))) && ((_x_s3_x <= 120.0) || ( !(( !(_x_s3_l2 != 0)) && ((_x_s3_l1 != 0) && ( !(_x_s3_l0 != 0))))))) && ((_x_s3_x <= 120.0) || ( !((_x_s3_l2 != 0) && ((_x_s3_l0 != 0) && ( !(_x_s3_l1 != 0))))))) && ((delta <= 0.0) || ((((delta + (s3_x + (-1.0 * _x_s3_x))) == 0.0) && ((delta + (s3_y + (-1.0 * _x_s3_y))) == 0.0)) && (((((s3_l0 != 0) == (_x_s3_l0 != 0)) && ((s3_l1 != 0) == (_x_s3_l1 != 0))) && ((s3_l2 != 0) == (_x_s3_l2 != 0))) && ((delta + (s3_z + (-1.0 * _x_s3_z))) == 0.0))))) && (((((((s3_l0 != 0) == (_x_s3_l0 != 0)) && ((s3_l1 != 0) == (_x_s3_l1 != 0))) && ((s3_l2 != 0) == (_x_s3_l2 != 0))) && ((delta + (s3_x + (-1.0 * _x_s3_x))) == 0.0)) && (((delta + (s3_y + (-1.0 * _x_s3_y))) == 0.0) && ((delta + (s3_z + (-1.0 * _x_s3_z))) == 0.0))) || ( !(( !(s3_evt0 != 0)) && ( !(s3_evt1 != 0)))))) && ((((((s3_evt0 != 0) && (s3_evt1 != 0)) && (( !(_x_s3_l2 != 0)) && ((_x_s3_l0 != 0) && ( !(_x_s3_l1 != 0))))) && ((_x_s3_x == 0.0) && (_x_s3_y == 0.0))) && (s3_z == _x_s3_z)) || ( !((( !(s3_l2 != 0)) && (( !(s3_l0 != 0)) && ( !(s3_l1 != 0)))) && ((delta == 0.0) && ( !(( !(s3_evt0 != 0)) && ( !(s3_evt1 != 0))))))))) && (((((( !(_x_s3_l2 != 0)) && ((_x_s3_l1 != 0) && ( !(_x_s3_l0 != 0)))) || (( !(_x_s3_l2 != 0)) && ((_x_s3_l0 != 0) && (_x_s3_l1 != 0)))) && (s3_x == _x_s3_x)) && ((s3_z == _x_s3_z) && (s3_y == _x_s3_y))) || ( !((( !(s3_l2 != 0)) && ((s3_l0 != 0) && ( !(s3_l1 != 0)))) && ((delta == 0.0) && ( !(( !(s3_evt0 != 0)) && ( !(s3_evt1 != 0))))))))) && ((((s3_evt0 != 0) && ( !(s3_evt1 != 0))) && ((20.0 <= s3_x) && ( !(120.0 <= s3_z)))) || ( !(((delta == 0.0) && ( !(( !(s3_evt0 != 0)) && ( !(s3_evt1 != 0))))) && ((( !(s3_l2 != 0)) && ((s3_l0 != 0) && ( !(s3_l1 != 0)))) && (( !(_x_s3_l2 != 0)) && ((_x_s3_l1 != 0) && ( !(_x_s3_l0 != 0))))))))) && ((((s3_evt1 != 0) && ( !(s3_evt0 != 0))) && ((20.0 <= s3_x) && (120.0 <= s3_z))) || ( !(((delta == 0.0) && ( !(( !(s3_evt0 != 0)) && ( !(s3_evt1 != 0))))) && ((( !(s3_l2 != 0)) && ((s3_l0 != 0) && ( !(s3_l1 != 0)))) && (( !(_x_s3_l2 != 0)) && ((_x_s3_l0 != 0) && (_x_s3_l1 != 0)))))))) && (((s3_z == _x_s3_z) && ((((s3_evt1 != 0) && ( !(s3_evt0 != 0))) && (( !(_x_s3_l2 != 0)) && ((_x_s3_l0 != 0) && (_x_s3_l1 != 0)))) && ((s3_x == _x_s3_x) && (s3_y == _x_s3_y)))) || ( !((( !(s3_l2 != 0)) && ((s3_l1 != 0) && ( !(s3_l0 != 0)))) && ((delta == 0.0) && ( !(( !(s3_evt0 != 0)) && ( !(s3_evt1 != 0))))))))) && ((((((s3_evt0 != 0) && (s3_evt1 != 0)) && ((_x_s3_l2 != 0) && (( !(_x_s3_l0 != 0)) && ( !(_x_s3_l1 != 0))))) && ((_x_s3_x == 0.0) && (s3_y == _x_s3_y))) && (_x_s3_z == 0.0)) || ( !((( !(s3_l2 != 0)) && ((s3_l0 != 0) && (s3_l1 != 0))) && ((delta == 0.0) && ( !(( !(s3_evt0 != 0)) && ( !(s3_evt1 != 0))))))))) && ((((s3_x == _x_s3_x) && (s3_y == _x_s3_y)) && ((s3_z == _x_s3_z) && ((( !(_x_s3_l2 != 0)) && (( !(_x_s3_l0 != 0)) && ( !(_x_s3_l1 != 0)))) || ((_x_s3_l2 != 0) && ((_x_s3_l0 != 0) && ( !(_x_s3_l1 != 0))))))) || ( !(((s3_l2 != 0) && (( !(s3_l0 != 0)) && ( !(s3_l1 != 0)))) && ((delta == 0.0) && ( !(( !(s3_evt0 != 0)) && ( !(s3_evt1 != 0))))))))) && ((((s3_evt0 != 0) && ( !(s3_evt1 != 0))) && ((20.0 <= s3_x) && ( !(120.0 <= s3_y)))) || ( !(((delta == 0.0) && ( !(( !(s3_evt0 != 0)) && ( !(s3_evt1 != 0))))) && (((s3_l2 != 0) && (( !(s3_l0 != 0)) && ( !(s3_l1 != 0)))) && ((_x_s3_l2 != 0) && ((_x_s3_l0 != 0) && ( !(_x_s3_l1 != 0))))))))) && ((((s3_evt1 != 0) && ( !(s3_evt0 != 0))) && ((20.0 <= s3_x) && (120.0 <= s3_y))) || ( !(((delta == 0.0) && ( !(( !(s3_evt0 != 0)) && ( !(s3_evt1 != 0))))) && ((( !(_x_s3_l2 != 0)) && (( !(_x_s3_l0 != 0)) && ( !(_x_s3_l1 != 0)))) && ((s3_l2 != 0) && (( !(s3_l0 != 0)) && ( !(s3_l1 != 0))))))))) && (((s3_z == _x_s3_z) && (((s3_x == _x_s3_x) && (s3_y == _x_s3_y)) && (((s3_evt1 != 0) && ( !(s3_evt0 != 0))) && (( !(_x_s3_l2 != 0)) && (( !(_x_s3_l0 != 0)) && ( !(_x_s3_l1 != 0))))))) || ( !(((s3_l2 != 0) && ((s3_l0 != 0) && ( !(s3_l1 != 0)))) && ((delta == 0.0) && ( !(( !(s3_evt0 != 0)) && ( !(s3_evt1 != 0))))))))) && ((((((((((((((((((((( !(_x_s2_evt0 != 0)) && ( !(_x_s2_evt1 != 0))) || ((_x_s2_evt0 != 0) && ( !(_x_s2_evt1 != 0)))) || (((_x_s2_evt1 != 0) && ( !(_x_s2_evt0 != 0))) || ((_x_s2_evt0 != 0) && (_x_s2_evt1 != 0)))) && ((((( !(_x_s2_l2 != 0)) && (( !(_x_s2_l0 != 0)) && ( !(_x_s2_l1 != 0)))) || (( !(_x_s2_l2 != 0)) && ((_x_s2_l0 != 0) && ( !(_x_s2_l1 != 0))))) || ((( !(_x_s2_l2 != 0)) && ((_x_s2_l1 != 0) && ( !(_x_s2_l0 != 0)))) || (( !(_x_s2_l2 != 0)) && ((_x_s2_l0 != 0) && (_x_s2_l1 != 0))))) || (((_x_s2_l2 != 0) && (( !(_x_s2_l0 != 0)) && ( !(_x_s2_l1 != 0)))) || ((_x_s2_l2 != 0) && ((_x_s2_l0 != 0) && ( !(_x_s2_l1 != 0))))))) && ((_x_s2_x <= 20.0) || ( !(( !(_x_s2_l2 != 0)) && ((_x_s2_l0 != 0) && ( !(_x_s2_l1 != 0))))))) && ((_x_s2_x <= 120.0) || ( !(( !(_x_s2_l2 != 0)) && ((_x_s2_l1 != 0) && ( !(_x_s2_l0 != 0))))))) && ((_x_s2_x <= 120.0) || ( !((_x_s2_l2 != 0) && ((_x_s2_l0 != 0) && ( !(_x_s2_l1 != 0))))))) && ((delta <= 0.0) || ((((delta + (s2_x + (-1.0 * _x_s2_x))) == 0.0) && ((delta + (s2_y + (-1.0 * _x_s2_y))) == 0.0)) && (((((s2_l0 != 0) == (_x_s2_l0 != 0)) && ((s2_l1 != 0) == (_x_s2_l1 != 0))) && ((s2_l2 != 0) == (_x_s2_l2 != 0))) && ((delta + (s2_z + (-1.0 * _x_s2_z))) == 0.0))))) && (((((((s2_l0 != 0) == (_x_s2_l0 != 0)) && ((s2_l1 != 0) == (_x_s2_l1 != 0))) && ((s2_l2 != 0) == (_x_s2_l2 != 0))) && ((delta + (s2_x + (-1.0 * _x_s2_x))) == 0.0)) && (((delta + (s2_y + (-1.0 * _x_s2_y))) == 0.0) && ((delta + (s2_z + (-1.0 * _x_s2_z))) == 0.0))) || ( !(( !(s2_evt0 != 0)) && ( !(s2_evt1 != 0)))))) && ((((((s2_evt0 != 0) && (s2_evt1 != 0)) && (( !(_x_s2_l2 != 0)) && ((_x_s2_l0 != 0) && ( !(_x_s2_l1 != 0))))) && ((_x_s2_x == 0.0) && (_x_s2_y == 0.0))) && (s2_z == _x_s2_z)) || ( !((( !(s2_l2 != 0)) && (( !(s2_l0 != 0)) && ( !(s2_l1 != 0)))) && ((delta == 0.0) && ( !(( !(s2_evt0 != 0)) && ( !(s2_evt1 != 0))))))))) && (((((( !(_x_s2_l2 != 0)) && ((_x_s2_l1 != 0) && ( !(_x_s2_l0 != 0)))) || (( !(_x_s2_l2 != 0)) && ((_x_s2_l0 != 0) && (_x_s2_l1 != 0)))) && (s2_x == _x_s2_x)) && ((s2_z == _x_s2_z) && (s2_y == _x_s2_y))) || ( !((( !(s2_l2 != 0)) && ((s2_l0 != 0) && ( !(s2_l1 != 0)))) && ((delta == 0.0) && ( !(( !(s2_evt0 != 0)) && ( !(s2_evt1 != 0))))))))) && ((((s2_evt0 != 0) && ( !(s2_evt1 != 0))) && ((20.0 <= s2_x) && ( !(120.0 <= s2_z)))) || ( !(((delta == 0.0) && ( !(( !(s2_evt0 != 0)) && ( !(s2_evt1 != 0))))) && ((( !(s2_l2 != 0)) && ((s2_l0 != 0) && ( !(s2_l1 != 0)))) && (( !(_x_s2_l2 != 0)) && ((_x_s2_l1 != 0) && ( !(_x_s2_l0 != 0))))))))) && ((((s2_evt1 != 0) && ( !(s2_evt0 != 0))) && ((20.0 <= s2_x) && (120.0 <= s2_z))) || ( !(((delta == 0.0) && ( !(( !(s2_evt0 != 0)) && ( !(s2_evt1 != 0))))) && ((( !(s2_l2 != 0)) && ((s2_l0 != 0) && ( !(s2_l1 != 0)))) && (( !(_x_s2_l2 != 0)) && ((_x_s2_l0 != 0) && (_x_s2_l1 != 0)))))))) && (((s2_z == _x_s2_z) && ((((s2_evt1 != 0) && ( !(s2_evt0 != 0))) && (( !(_x_s2_l2 != 0)) && ((_x_s2_l0 != 0) && (_x_s2_l1 != 0)))) && ((s2_x == _x_s2_x) && (s2_y == _x_s2_y)))) || ( !((( !(s2_l2 != 0)) && ((s2_l1 != 0) && ( !(s2_l0 != 0)))) && ((delta == 0.0) && ( !(( !(s2_evt0 != 0)) && ( !(s2_evt1 != 0))))))))) && ((((((s2_evt0 != 0) && (s2_evt1 != 0)) && ((_x_s2_l2 != 0) && (( !(_x_s2_l0 != 0)) && ( !(_x_s2_l1 != 0))))) && ((_x_s2_x == 0.0) && (s2_y == _x_s2_y))) && (_x_s2_z == 0.0)) || ( !((( !(s2_l2 != 0)) && ((s2_l0 != 0) && (s2_l1 != 0))) && ((delta == 0.0) && ( !(( !(s2_evt0 != 0)) && ( !(s2_evt1 != 0))))))))) && ((((s2_x == _x_s2_x) && (s2_y == _x_s2_y)) && ((s2_z == _x_s2_z) && ((( !(_x_s2_l2 != 0)) && (( !(_x_s2_l0 != 0)) && ( !(_x_s2_l1 != 0)))) || ((_x_s2_l2 != 0) && ((_x_s2_l0 != 0) && ( !(_x_s2_l1 != 0))))))) || ( !(((s2_l2 != 0) && (( !(s2_l0 != 0)) && ( !(s2_l1 != 0)))) && ((delta == 0.0) && ( !(( !(s2_evt0 != 0)) && ( !(s2_evt1 != 0))))))))) && ((((s2_evt0 != 0) && ( !(s2_evt1 != 0))) && ((20.0 <= s2_x) && ( !(120.0 <= s2_y)))) || ( !(((delta == 0.0) && ( !(( !(s2_evt0 != 0)) && ( !(s2_evt1 != 0))))) && (((s2_l2 != 0) && (( !(s2_l0 != 0)) && ( !(s2_l1 != 0)))) && ((_x_s2_l2 != 0) && ((_x_s2_l0 != 0) && ( !(_x_s2_l1 != 0))))))))) && ((((s2_evt1 != 0) && ( !(s2_evt0 != 0))) && ((20.0 <= s2_x) && (120.0 <= s2_y))) || ( !(((delta == 0.0) && ( !(( !(s2_evt0 != 0)) && ( !(s2_evt1 != 0))))) && ((( !(_x_s2_l2 != 0)) && (( !(_x_s2_l0 != 0)) && ( !(_x_s2_l1 != 0)))) && ((s2_l2 != 0) && (( !(s2_l0 != 0)) && ( !(s2_l1 != 0))))))))) && (((s2_z == _x_s2_z) && (((s2_x == _x_s2_x) && (s2_y == _x_s2_y)) && (((s2_evt1 != 0) && ( !(s2_evt0 != 0))) && (( !(_x_s2_l2 != 0)) && (( !(_x_s2_l0 != 0)) && ( !(_x_s2_l1 != 0))))))) || ( !(((s2_l2 != 0) && ((s2_l0 != 0) && ( !(s2_l1 != 0)))) && ((delta == 0.0) && ( !(( !(s2_evt0 != 0)) && ( !(s2_evt1 != 0))))))))) && ((((((((((((((((((((( !(_x_s1_evt0 != 0)) && ( !(_x_s1_evt1 != 0))) || ((_x_s1_evt0 != 0) && ( !(_x_s1_evt1 != 0)))) || (((_x_s1_evt1 != 0) && ( !(_x_s1_evt0 != 0))) || ((_x_s1_evt0 != 0) && (_x_s1_evt1 != 0)))) && ((((( !(_x_s1_l2 != 0)) && (( !(_x_s1_l0 != 0)) && ( !(_x_s1_l1 != 0)))) || (( !(_x_s1_l2 != 0)) && ((_x_s1_l0 != 0) && ( !(_x_s1_l1 != 0))))) || ((( !(_x_s1_l2 != 0)) && ((_x_s1_l1 != 0) && ( !(_x_s1_l0 != 0)))) || (( !(_x_s1_l2 != 0)) && ((_x_s1_l0 != 0) && (_x_s1_l1 != 0))))) || (((_x_s1_l2 != 0) && (( !(_x_s1_l0 != 0)) && ( !(_x_s1_l1 != 0)))) || ((_x_s1_l2 != 0) && ((_x_s1_l0 != 0) && ( !(_x_s1_l1 != 0))))))) && ((_x_s1_x <= 20.0) || ( !(( !(_x_s1_l2 != 0)) && ((_x_s1_l0 != 0) && ( !(_x_s1_l1 != 0))))))) && ((_x_s1_x <= 120.0) || ( !(( !(_x_s1_l2 != 0)) && ((_x_s1_l1 != 0) && ( !(_x_s1_l0 != 0))))))) && ((_x_s1_x <= 120.0) || ( !((_x_s1_l2 != 0) && ((_x_s1_l0 != 0) && ( !(_x_s1_l1 != 0))))))) && ((delta <= 0.0) || ((((delta + (s1_x + (-1.0 * _x_s1_x))) == 0.0) && ((delta + (s1_y + (-1.0 * _x_s1_y))) == 0.0)) && (((((s1_l0 != 0) == (_x_s1_l0 != 0)) && ((s1_l1 != 0) == (_x_s1_l1 != 0))) && ((s1_l2 != 0) == (_x_s1_l2 != 0))) && ((delta + (s1_z + (-1.0 * _x_s1_z))) == 0.0))))) && (((((((s1_l0 != 0) == (_x_s1_l0 != 0)) && ((s1_l1 != 0) == (_x_s1_l1 != 0))) && ((s1_l2 != 0) == (_x_s1_l2 != 0))) && ((delta + (s1_x + (-1.0 * _x_s1_x))) == 0.0)) && (((delta + (s1_y + (-1.0 * _x_s1_y))) == 0.0) && ((delta + (s1_z + (-1.0 * _x_s1_z))) == 0.0))) || ( !(( !(s1_evt0 != 0)) && ( !(s1_evt1 != 0)))))) && ((((((s1_evt0 != 0) && (s1_evt1 != 0)) && (( !(_x_s1_l2 != 0)) && ((_x_s1_l0 != 0) && ( !(_x_s1_l1 != 0))))) && ((_x_s1_x == 0.0) && (_x_s1_y == 0.0))) && (s1_z == _x_s1_z)) || ( !((( !(s1_l2 != 0)) && (( !(s1_l0 != 0)) && ( !(s1_l1 != 0)))) && ((delta == 0.0) && ( !(( !(s1_evt0 != 0)) && ( !(s1_evt1 != 0))))))))) && (((((( !(_x_s1_l2 != 0)) && ((_x_s1_l1 != 0) && ( !(_x_s1_l0 != 0)))) || (( !(_x_s1_l2 != 0)) && ((_x_s1_l0 != 0) && (_x_s1_l1 != 0)))) && (s1_x == _x_s1_x)) && ((s1_z == _x_s1_z) && (s1_y == _x_s1_y))) || ( !((( !(s1_l2 != 0)) && ((s1_l0 != 0) && ( !(s1_l1 != 0)))) && ((delta == 0.0) && ( !(( !(s1_evt0 != 0)) && ( !(s1_evt1 != 0))))))))) && ((((s1_evt0 != 0) && ( !(s1_evt1 != 0))) && ((20.0 <= s1_x) && ( !(120.0 <= s1_z)))) || ( !(((delta == 0.0) && ( !(( !(s1_evt0 != 0)) && ( !(s1_evt1 != 0))))) && ((( !(s1_l2 != 0)) && ((s1_l0 != 0) && ( !(s1_l1 != 0)))) && (( !(_x_s1_l2 != 0)) && ((_x_s1_l1 != 0) && ( !(_x_s1_l0 != 0))))))))) && ((((s1_evt1 != 0) && ( !(s1_evt0 != 0))) && ((20.0 <= s1_x) && (120.0 <= s1_z))) || ( !(((delta == 0.0) && ( !(( !(s1_evt0 != 0)) && ( !(s1_evt1 != 0))))) && ((( !(s1_l2 != 0)) && ((s1_l0 != 0) && ( !(s1_l1 != 0)))) && (( !(_x_s1_l2 != 0)) && ((_x_s1_l0 != 0) && (_x_s1_l1 != 0)))))))) && (((s1_z == _x_s1_z) && ((((s1_evt1 != 0) && ( !(s1_evt0 != 0))) && (( !(_x_s1_l2 != 0)) && ((_x_s1_l0 != 0) && (_x_s1_l1 != 0)))) && ((s1_x == _x_s1_x) && (s1_y == _x_s1_y)))) || ( !((( !(s1_l2 != 0)) && ((s1_l1 != 0) && ( !(s1_l0 != 0)))) && ((delta == 0.0) && ( !(( !(s1_evt0 != 0)) && ( !(s1_evt1 != 0))))))))) && ((((((s1_evt0 != 0) && (s1_evt1 != 0)) && ((_x_s1_l2 != 0) && (( !(_x_s1_l0 != 0)) && ( !(_x_s1_l1 != 0))))) && ((_x_s1_x == 0.0) && (s1_y == _x_s1_y))) && (_x_s1_z == 0.0)) || ( !((( !(s1_l2 != 0)) && ((s1_l0 != 0) && (s1_l1 != 0))) && ((delta == 0.0) && ( !(( !(s1_evt0 != 0)) && ( !(s1_evt1 != 0))))))))) && ((((s1_x == _x_s1_x) && (s1_y == _x_s1_y)) && ((s1_z == _x_s1_z) && ((( !(_x_s1_l2 != 0)) && (( !(_x_s1_l0 != 0)) && ( !(_x_s1_l1 != 0)))) || ((_x_s1_l2 != 0) && ((_x_s1_l0 != 0) && ( !(_x_s1_l1 != 0))))))) || ( !(((s1_l2 != 0) && (( !(s1_l0 != 0)) && ( !(s1_l1 != 0)))) && ((delta == 0.0) && ( !(( !(s1_evt0 != 0)) && ( !(s1_evt1 != 0))))))))) && ((((s1_evt0 != 0) && ( !(s1_evt1 != 0))) && ((20.0 <= s1_x) && ( !(120.0 <= s1_y)))) || ( !(((delta == 0.0) && ( !(( !(s1_evt0 != 0)) && ( !(s1_evt1 != 0))))) && (((s1_l2 != 0) && (( !(s1_l0 != 0)) && ( !(s1_l1 != 0)))) && ((_x_s1_l2 != 0) && ((_x_s1_l0 != 0) && ( !(_x_s1_l1 != 0))))))))) && ((((s1_evt1 != 0) && ( !(s1_evt0 != 0))) && ((20.0 <= s1_x) && (120.0 <= s1_y))) || ( !(((delta == 0.0) && ( !(( !(s1_evt0 != 0)) && ( !(s1_evt1 != 0))))) && ((( !(_x_s1_l2 != 0)) && (( !(_x_s1_l0 != 0)) && ( !(_x_s1_l1 != 0)))) && ((s1_l2 != 0) && (( !(s1_l0 != 0)) && ( !(s1_l1 != 0))))))))) && (((s1_z == _x_s1_z) && (((s1_x == _x_s1_x) && (s1_y == _x_s1_y)) && (((s1_evt1 != 0) && ( !(s1_evt0 != 0))) && (( !(_x_s1_l2 != 0)) && (( !(_x_s1_l0 != 0)) && ( !(_x_s1_l1 != 0))))))) || ( !(((s1_l2 != 0) && ((s1_l0 != 0) && ( !(s1_l1 != 0)))) && ((delta == 0.0) && ( !(( !(s1_evt0 != 0)) && ( !(s1_evt1 != 0))))))))) && ((((((((((((((((((((( !(_x_s0_evt0 != 0)) && ( !(_x_s0_evt1 != 0))) || ((_x_s0_evt0 != 0) && ( !(_x_s0_evt1 != 0)))) || (((_x_s0_evt1 != 0) && ( !(_x_s0_evt0 != 0))) || ((_x_s0_evt0 != 0) && (_x_s0_evt1 != 0)))) && ((((( !(_x_s0_l2 != 0)) && (( !(_x_s0_l0 != 0)) && ( !(_x_s0_l1 != 0)))) || (( !(_x_s0_l2 != 0)) && ((_x_s0_l0 != 0) && ( !(_x_s0_l1 != 0))))) || ((( !(_x_s0_l2 != 0)) && ((_x_s0_l1 != 0) && ( !(_x_s0_l0 != 0)))) || (( !(_x_s0_l2 != 0)) && ((_x_s0_l0 != 0) && (_x_s0_l1 != 0))))) || (((_x_s0_l2 != 0) && (( !(_x_s0_l0 != 0)) && ( !(_x_s0_l1 != 0)))) || ((_x_s0_l2 != 0) && ((_x_s0_l0 != 0) && ( !(_x_s0_l1 != 0))))))) && ((_x_s0_x <= 20.0) || ( !(( !(_x_s0_l2 != 0)) && ((_x_s0_l0 != 0) && ( !(_x_s0_l1 != 0))))))) && ((_x_s0_x <= 120.0) || ( !(( !(_x_s0_l2 != 0)) && ((_x_s0_l1 != 0) && ( !(_x_s0_l0 != 0))))))) && ((_x_s0_x <= 120.0) || ( !((_x_s0_l2 != 0) && ((_x_s0_l0 != 0) && ( !(_x_s0_l1 != 0))))))) && ((delta <= 0.0) || ((((delta + (s0_x + (-1.0 * _x_s0_x))) == 0.0) && ((delta + (s0_y + (-1.0 * _x_s0_y))) == 0.0)) && (((((s0_l0 != 0) == (_x_s0_l0 != 0)) && ((s0_l1 != 0) == (_x_s0_l1 != 0))) && ((s0_l2 != 0) == (_x_s0_l2 != 0))) && ((delta + (s0_z + (-1.0 * _x_s0_z))) == 0.0))))) && (((((((s0_l0 != 0) == (_x_s0_l0 != 0)) && ((s0_l1 != 0) == (_x_s0_l1 != 0))) && ((s0_l2 != 0) == (_x_s0_l2 != 0))) && ((delta + (s0_x + (-1.0 * _x_s0_x))) == 0.0)) && (((delta + (s0_y + (-1.0 * _x_s0_y))) == 0.0) && ((delta + (s0_z + (-1.0 * _x_s0_z))) == 0.0))) || ( !(( !(s0_evt0 != 0)) && ( !(s0_evt1 != 0)))))) && ((((((s0_evt0 != 0) && (s0_evt1 != 0)) && (( !(_x_s0_l2 != 0)) && ((_x_s0_l0 != 0) && ( !(_x_s0_l1 != 0))))) && ((_x_s0_x == 0.0) && (_x_s0_y == 0.0))) && (s0_z == _x_s0_z)) || ( !((( !(s0_l2 != 0)) && (( !(s0_l0 != 0)) && ( !(s0_l1 != 0)))) && ((delta == 0.0) && ( !(( !(s0_evt0 != 0)) && ( !(s0_evt1 != 0))))))))) && (((((( !(_x_s0_l2 != 0)) && ((_x_s0_l1 != 0) && ( !(_x_s0_l0 != 0)))) || (( !(_x_s0_l2 != 0)) && ((_x_s0_l0 != 0) && (_x_s0_l1 != 0)))) && (s0_x == _x_s0_x)) && ((s0_z == _x_s0_z) && (s0_y == _x_s0_y))) || ( !((( !(s0_l2 != 0)) && ((s0_l0 != 0) && ( !(s0_l1 != 0)))) && ((delta == 0.0) && ( !(( !(s0_evt0 != 0)) && ( !(s0_evt1 != 0))))))))) && ((((s0_evt0 != 0) && ( !(s0_evt1 != 0))) && ((20.0 <= s0_x) && ( !(120.0 <= s0_z)))) || ( !(((delta == 0.0) && ( !(( !(s0_evt0 != 0)) && ( !(s0_evt1 != 0))))) && ((( !(s0_l2 != 0)) && ((s0_l0 != 0) && ( !(s0_l1 != 0)))) && (( !(_x_s0_l2 != 0)) && ((_x_s0_l1 != 0) && ( !(_x_s0_l0 != 0))))))))) && ((((s0_evt1 != 0) && ( !(s0_evt0 != 0))) && ((20.0 <= s0_x) && (120.0 <= s0_z))) || ( !(((delta == 0.0) && ( !(( !(s0_evt0 != 0)) && ( !(s0_evt1 != 0))))) && ((( !(s0_l2 != 0)) && ((s0_l0 != 0) && ( !(s0_l1 != 0)))) && (( !(_x_s0_l2 != 0)) && ((_x_s0_l0 != 0) && (_x_s0_l1 != 0)))))))) && (((s0_z == _x_s0_z) && ((((s0_evt1 != 0) && ( !(s0_evt0 != 0))) && (( !(_x_s0_l2 != 0)) && ((_x_s0_l0 != 0) && (_x_s0_l1 != 0)))) && ((s0_x == _x_s0_x) && (s0_y == _x_s0_y)))) || ( !((( !(s0_l2 != 0)) && ((s0_l1 != 0) && ( !(s0_l0 != 0)))) && ((delta == 0.0) && ( !(( !(s0_evt0 != 0)) && ( !(s0_evt1 != 0))))))))) && ((((((s0_evt0 != 0) && (s0_evt1 != 0)) && ((_x_s0_l2 != 0) && (( !(_x_s0_l0 != 0)) && ( !(_x_s0_l1 != 0))))) && ((_x_s0_x == 0.0) && (s0_y == _x_s0_y))) && (_x_s0_z == 0.0)) || ( !((( !(s0_l2 != 0)) && ((s0_l0 != 0) && (s0_l1 != 0))) && ((delta == 0.0) && ( !(( !(s0_evt0 != 0)) && ( !(s0_evt1 != 0))))))))) && ((((s0_x == _x_s0_x) && (s0_y == _x_s0_y)) && ((s0_z == _x_s0_z) && ((( !(_x_s0_l2 != 0)) && (( !(_x_s0_l0 != 0)) && ( !(_x_s0_l1 != 0)))) || ((_x_s0_l2 != 0) && ((_x_s0_l0 != 0) && ( !(_x_s0_l1 != 0))))))) || ( !(((s0_l2 != 0) && (( !(s0_l0 != 0)) && ( !(s0_l1 != 0)))) && ((delta == 0.0) && ( !(( !(s0_evt0 != 0)) && ( !(s0_evt1 != 0))))))))) && ((((s0_evt0 != 0) && ( !(s0_evt1 != 0))) && ((20.0 <= s0_x) && ( !(120.0 <= s0_y)))) || ( !(((delta == 0.0) && ( !(( !(s0_evt0 != 0)) && ( !(s0_evt1 != 0))))) && (((s0_l2 != 0) && (( !(s0_l0 != 0)) && ( !(s0_l1 != 0)))) && ((_x_s0_l2 != 0) && ((_x_s0_l0 != 0) && ( !(_x_s0_l1 != 0))))))))) && ((((s0_evt1 != 0) && ( !(s0_evt0 != 0))) && ((20.0 <= s0_x) && (120.0 <= s0_y))) || ( !(((delta == 0.0) && ( !(( !(s0_evt0 != 0)) && ( !(s0_evt1 != 0))))) && ((( !(_x_s0_l2 != 0)) && (( !(_x_s0_l0 != 0)) && ( !(_x_s0_l1 != 0)))) && ((s0_l2 != 0) && (( !(s0_l0 != 0)) && ( !(s0_l1 != 0))))))))) && (((s0_z == _x_s0_z) && (((s0_x == _x_s0_x) && (s0_y == _x_s0_y)) && (((s0_evt1 != 0) && ( !(s0_evt0 != 0))) && (( !(_x_s0_l2 != 0)) && (( !(_x_s0_l0 != 0)) && ( !(_x_s0_l1 != 0))))))) || ( !(((s0_l2 != 0) && ((s0_l0 != 0) && ( !(s0_l1 != 0)))) && ((delta == 0.0) && ( !(( !(s0_evt0 != 0)) && ( !(s0_evt1 != 0))))))))) && (((((((((((((_x_r_evt_id == 0) || (_x_r_evt_id == 1)) || (_x_r_evt_id == 2)) || (_x_r_evt_id == 3)) || (_x_r_evt_id == 4)) && (((((_x_r_counter == 0) || (_x_r_counter == 1)) || (_x_r_counter == 2)) || (_x_r_counter == 3)) || (_x_r_counter == 4))) && (( !(_x_r_l != 0)) || (_x_r_x <= 0.0))) && ((delta <= 0.0) || (((delta + (r_x + (-1.0 * _x_r_x))) == 0.0) && (((r_l != 0) == (_x_r_l != 0)) && (r_counter == _x_r_counter))))) && ((((r_l != 0) == (_x_r_l != 0)) && (((delta + (r_x + (-1.0 * _x_r_x))) == 0.0) && (r_counter == _x_r_counter))) || ( !(( !(r_event0 != 0)) && ( !(r_event1 != 0)))))) && ((((((r_event1 != 0) && ( !(r_event0 != 0))) && (r_x <= 0.0)) && (( !(_x_r_l != 0)) && (r_evt_id == r_counter))) && ((r_counter == _x_r_counter) && (r_x == _x_r_x))) || ( !((r_l != 0) && (( !(( !(r_event0 != 0)) && ( !(r_event1 != 0)))) && (delta == 0.0)))))) && (((_x_r_l != 0) && ((((r_event0 != 0) && ( !(r_event1 != 0))) && (r_evt_id == r_counter)) && ((_x_r_x == 0.0) && ((r_counter + (-1 * _x_r_counter)) == -1)))) || ( !((( !(( !(r_event0 != 0)) && ( !(r_event1 != 0)))) && (delta == 0.0)) && (( !(r_l != 0)) && ( !(4 <= r_counter))))))) && (((_x_r_l != 0) && ((((r_event0 != 0) && ( !(r_event1 != 0))) && (r_evt_id == r_counter)) && ((_x_r_counter == 0) && (_x_r_x == 0.0)))) || ( !((( !(( !(r_event0 != 0)) && ( !(r_event1 != 0)))) && (delta == 0.0)) && (( !(r_l != 0)) && (r_counter == 4)))))) && (0.0 <= _x_delta))))))) && ((( !(( !(s4_evt0 != 0)) && ( !(s4_evt1 != 0)))) || (( !(( !(s3_evt0 != 0)) && ( !(s3_evt1 != 0)))) || (( !(( !(s2_evt0 != 0)) && ( !(s2_evt1 != 0)))) || (( !(( !(s1_evt0 != 0)) && ( !(s1_evt1 != 0)))) || (( !(( !(r_event0 != 0)) && ( !(r_event1 != 0)))) || ( !(( !(s0_evt0 != 0)) && ( !(s0_evt1 != 0))))))))) || ( !(delta == 0.0)))) && (( !(delta == 0.0)) || (((s0_evt1 != 0) && ( !(s0_evt0 != 0))) == (((r_event0 != 0) && ( !(r_event1 != 0))) && (r_evt_id == 0))))) && (( !(delta == 0.0)) || (((s0_evt0 != 0) && (s0_evt1 != 0)) == (((r_event1 != 0) && ( !(r_event0 != 0))) && (r_evt_id == 0))))) && (( !(delta == 0.0)) || (((s1_evt1 != 0) && ( !(s1_evt0 != 0))) == (((r_event0 != 0) && ( !(r_event1 != 0))) && (r_evt_id == 1))))) && (( !(delta == 0.0)) || (((s1_evt0 != 0) && (s1_evt1 != 0)) == (((r_event1 != 0) && ( !(r_event0 != 0))) && (r_evt_id == 1))))) && (( !(delta == 0.0)) || (((s2_evt1 != 0) && ( !(s2_evt0 != 0))) == (((r_event0 != 0) && ( !(r_event1 != 0))) && (r_evt_id == 2))))) && (( !(delta == 0.0)) || (((s2_evt0 != 0) && (s2_evt1 != 0)) == (((r_event1 != 0) && ( !(r_event0 != 0))) && (r_evt_id == 2))))) && (( !(delta == 0.0)) || (((s3_evt1 != 0) && ( !(s3_evt0 != 0))) == (((r_event0 != 0) && ( !(r_event1 != 0))) && (r_evt_id == 3))))) && (( !(delta == 0.0)) || (((s3_evt0 != 0) && (s3_evt1 != 0)) == (((r_event1 != 0) && ( !(r_event0 != 0))) && (r_evt_id == 3))))) && (( !(delta == 0.0)) || (((s4_evt1 != 0) && ( !(s4_evt0 != 0))) == (((r_event0 != 0) && ( !(r_event1 != 0))) && (r_evt_id == 4))))) && (( !(delta == 0.0)) || (((s4_evt0 != 0) && (s4_evt1 != 0)) == (((r_event1 != 0) && ( !(r_event0 != 0))) && (r_evt_id == 4))))) && (((delta == _x__diverge_delta) || ( !(1.0 <= _diverge_delta))) && ((1.0 <= _diverge_delta) || ((delta + (_diverge_delta + (-1.0 * _x__diverge_delta))) == 0.0))));
    _diverge_delta = _x__diverge_delta;
    s4_l2 = _x_s4_l2;
    s4_evt1 = _x_s4_evt1;
    s4_z = _x_s4_z;
    s3_l2 = _x_s3_l2;
    s3_l1 = _x_s3_l1;
    s3_l0 = _x_s3_l0;
    s3_evt1 = _x_s3_evt1;
    s3_evt0 = _x_s3_evt0;
    s3_y = _x_s3_y;
    s3_x = _x_s3_x;
    s2_l2 = _x_s2_l2;
    s2_l1 = _x_s2_l1;
    s0_l0 = _x_s0_l0;
    s2_l0 = _x_s2_l0;
    s2_evt1 = _x_s2_evt1;
    s2_evt0 = _x_s2_evt0;
    s0_z = _x_s0_z;
    s3_z = _x_s3_z;
    r_l = _x_r_l;
    s2_z = _x_s2_z;
    s0_y = _x_s0_y;
    s2_y = _x_s2_y;
    s0_x = _x_s0_x;
    s2_x = _x_s2_x;
    s4_y = _x_s4_y;
    s1_z = _x_s1_z;
    s1_l0 = _x_s1_l0;
    r_evt_id = _x_r_evt_id;
    delta = _x_delta;
    s4_x = _x_s4_x;
    s1_y = _x_s1_y;
    s0_l1 = _x_s0_l1;
    s0_l2 = _x_s0_l2;
    s1_x = _x_s1_x;
    r_event0 = _x_r_event0;
    s1_evt0 = _x_s1_evt0;
    s4_evt0 = _x_s4_evt0;
    r_event1 = _x_r_event1;
    s1_evt1 = _x_s1_evt1;
    s4_l0 = _x_s4_l0;
    s0_evt0 = _x_s0_evt0;
    r_counter = _x_r_counter;
    s1_l1 = _x_s1_l1;
    s4_l1 = _x_s4_l1;
    s0_evt1 = _x_s0_evt1;
    r_x = _x_r_x;
    s1_l2 = _x_s1_l2;

  }
}