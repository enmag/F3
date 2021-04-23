//@ ltl invariant negative: ( (<> ([] AP((inc_max_prop != 0)))) || (! ([] (<> AP((1.0 <= _diverge_delta))))));

extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);

char __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}


float p3_saved_max, _x_p3_saved_max;
float p3_x, _x_p3_x;
char p2_l1, _x_p2_l1;
char p2_l0, _x_p2_l0;
float p2_saved_max, _x_p2_saved_max;
char p0_l1, _x_p0_l1;
char p0_l0, _x_p0_l0;
float p0_saved_max, _x_p0_saved_max;
float max_prop, _x_max_prop;
char p3_l0, _x_p3_l0;
char id1, _x_id1;
float delta, _x_delta;
char p3_l1, _x_p3_l1;
char id2, _x_id2;
float _diverge_delta, _x__diverge_delta;
char p1_l0, _x_p1_l0;
char turn0, _x_turn0;
float p2_x, _x_p2_x;
char p1_l1, _x_p1_l1;
char turn1, _x_turn1;
float p0_x, _x_p0_x;
char inc_max_prop, _x_inc_max_prop;
char id0, _x_id0;
float proposed3, _x_proposed3;
float p1_x, _x_p1_x;
float proposed0, _x_proposed0;
float p1_saved_max, _x_p1_saved_max;
float proposed1, _x_proposed1;
float proposed2, _x_proposed2;

int main()
{
  p3_saved_max = __VERIFIER_nondet_float();
  p3_x = __VERIFIER_nondet_float();
  p2_l1 = __VERIFIER_nondet_bool();
  p2_l0 = __VERIFIER_nondet_bool();
  p2_saved_max = __VERIFIER_nondet_float();
  p0_l1 = __VERIFIER_nondet_bool();
  p0_l0 = __VERIFIER_nondet_bool();
  p0_saved_max = __VERIFIER_nondet_float();
  max_prop = __VERIFIER_nondet_float();
  p3_l0 = __VERIFIER_nondet_bool();
  id1 = __VERIFIER_nondet_bool();
  delta = __VERIFIER_nondet_float();
  p3_l1 = __VERIFIER_nondet_bool();
  id2 = __VERIFIER_nondet_bool();
  _diverge_delta = __VERIFIER_nondet_float();
  p1_l0 = __VERIFIER_nondet_bool();
  turn0 = __VERIFIER_nondet_bool();
  p2_x = __VERIFIER_nondet_float();
  p1_l1 = __VERIFIER_nondet_bool();
  turn1 = __VERIFIER_nondet_bool();
  p0_x = __VERIFIER_nondet_float();
  inc_max_prop = __VERIFIER_nondet_bool();
  id0 = __VERIFIER_nondet_bool();
  proposed3 = __VERIFIER_nondet_float();
  p1_x = __VERIFIER_nondet_float();
  proposed0 = __VERIFIER_nondet_float();
  p1_saved_max = __VERIFIER_nondet_float();
  proposed1 = __VERIFIER_nondet_float();
  proposed2 = __VERIFIER_nondet_float();

  int __ok = (((((((( !(p3_l0 != 0)) && ( !(p3_l1 != 0))) && (((( !(p3_l0 != 0)) && ( !(p3_l1 != 0))) || ((p3_l0 != 0) && ( !(p3_l1 != 0)))) || (((p3_l1 != 0) && ( !(p3_l0 != 0))) || ((p3_l0 != 0) && (p3_l1 != 0))))) && ((p3_x == 0.0) && (max_prop == p3_saved_max))) && ( !(proposed3 <= 0.0))) && ((p3_x <= proposed3) || ( !((p3_l1 != 0) && ( !(p3_l0 != 0)))))) && ((((((( !(p2_l0 != 0)) && ( !(p2_l1 != 0))) && (((( !(p2_l0 != 0)) && ( !(p2_l1 != 0))) || ((p2_l0 != 0) && ( !(p2_l1 != 0)))) || (((p2_l1 != 0) && ( !(p2_l0 != 0))) || ((p2_l0 != 0) && (p2_l1 != 0))))) && ((p2_x == 0.0) && (max_prop == p2_saved_max))) && ( !(proposed2 <= 0.0))) && ((p2_x <= proposed2) || ( !((p2_l1 != 0) && ( !(p2_l0 != 0)))))) && ((((((( !(p1_l0 != 0)) && ( !(p1_l1 != 0))) && (((( !(p1_l0 != 0)) && ( !(p1_l1 != 0))) || ((p1_l0 != 0) && ( !(p1_l1 != 0)))) || (((p1_l1 != 0) && ( !(p1_l0 != 0))) || ((p1_l0 != 0) && (p1_l1 != 0))))) && ((p1_x == 0.0) && (max_prop == p1_saved_max))) && ( !(proposed1 <= 0.0))) && ((p1_x <= proposed1) || ( !((p1_l1 != 0) && ( !(p1_l0 != 0)))))) && ((((((( !(p0_l0 != 0)) && ( !(p0_l1 != 0))) && (((( !(p0_l0 != 0)) && ( !(p0_l1 != 0))) || ((p0_l0 != 0) && ( !(p0_l1 != 0)))) || (((p0_l1 != 0) && ( !(p0_l0 != 0))) || ((p0_l0 != 0) && (p0_l1 != 0))))) && ((p0_x == 0.0) && (max_prop == p0_saved_max))) && ( !(proposed0 <= 0.0))) && ((p0_x <= proposed0) || ( !((p0_l1 != 0) && ( !(p0_l0 != 0)))))) && (((((((((((id2 != 0) && (( !(id0 != 0)) && ( !(id1 != 0)))) || ((( !(id2 != 0)) && ((id0 != 0) && (id1 != 0))) || ((( !(id2 != 0)) && ((id1 != 0) && ( !(id0 != 0)))) || ((( !(id2 != 0)) && (( !(id0 != 0)) && ( !(id1 != 0)))) || (( !(id2 != 0)) && ((id0 != 0) && ( !(id1 != 0)))))))) && (((turn0 != 0) && (turn1 != 0)) || (((turn1 != 0) && ( !(turn0 != 0))) || ((( !(turn0 != 0)) && ( !(turn1 != 0))) || ((turn0 != 0) && ( !(turn1 != 0))))))) && ((( !(id2 != 0)) && (( !(id0 != 0)) && ( !(id1 != 0)))) && (inc_max_prop != 0))) && (0.0 <= delta)) && (proposed0 <= max_prop)) && (proposed1 <= max_prop)) && (proposed2 <= max_prop)) && (proposed3 <= max_prop)) && ((((proposed0 == max_prop) || (proposed1 == max_prop)) || (proposed2 == max_prop)) || (proposed3 == max_prop))))))) && (delta == _diverge_delta));
  while (__ok) {
    _x_p3_saved_max = __VERIFIER_nondet_float();
    _x_p3_x = __VERIFIER_nondet_float();
    _x_p2_l1 = __VERIFIER_nondet_bool();
    _x_p2_l0 = __VERIFIER_nondet_bool();
    _x_p2_saved_max = __VERIFIER_nondet_float();
    _x_p0_l1 = __VERIFIER_nondet_bool();
    _x_p0_l0 = __VERIFIER_nondet_bool();
    _x_p0_saved_max = __VERIFIER_nondet_float();
    _x_max_prop = __VERIFIER_nondet_float();
    _x_p3_l0 = __VERIFIER_nondet_bool();
    _x_id1 = __VERIFIER_nondet_bool();
    _x_delta = __VERIFIER_nondet_float();
    _x_p3_l1 = __VERIFIER_nondet_bool();
    _x_id2 = __VERIFIER_nondet_bool();
    _x__diverge_delta = __VERIFIER_nondet_float();
    _x_p1_l0 = __VERIFIER_nondet_bool();
    _x_turn0 = __VERIFIER_nondet_bool();
    _x_p2_x = __VERIFIER_nondet_float();
    _x_p1_l1 = __VERIFIER_nondet_bool();
    _x_turn1 = __VERIFIER_nondet_bool();
    _x_p0_x = __VERIFIER_nondet_float();
    _x_inc_max_prop = __VERIFIER_nondet_bool();
    _x_id0 = __VERIFIER_nondet_bool();
    _x_proposed3 = __VERIFIER_nondet_float();
    _x_p1_x = __VERIFIER_nondet_float();
    _x_proposed0 = __VERIFIER_nondet_float();
    _x_p1_saved_max = __VERIFIER_nondet_float();
    _x_proposed1 = __VERIFIER_nondet_float();
    _x_proposed2 = __VERIFIER_nondet_float();

    __ok = ((((((((((((( !(_x_p3_l0 != 0)) && ( !(_x_p3_l1 != 0))) || ((_x_p3_l0 != 0) && ( !(_x_p3_l1 != 0)))) || (((_x_p3_l1 != 0) && ( !(_x_p3_l0 != 0))) || ((_x_p3_l0 != 0) && (_x_p3_l1 != 0)))) && ( !(_x_proposed3 <= 0.0))) && ((_x_p3_x <= _x_proposed3) || ( !((_x_p3_l1 != 0) && ( !(_x_p3_l0 != 0)))))) && ((((((p3_l0 != 0) == (_x_p3_l0 != 0)) && ((p3_l1 != 0) == (_x_p3_l1 != 0))) && ((delta + (p3_x + (-1.0 * _x_p3_x))) == 0.0)) && ((p3_saved_max == _x_p3_saved_max) && (proposed3 == _x_proposed3))) || ( !(( !(delta <= 0.0)) || ( !((turn0 != 0) && (turn1 != 0))))))) && ((((((_x_p3_l1 != 0) && ( !(_x_p3_l0 != 0))) && (_x_p3_x == 0.0)) && (((((id0 != 0) == (_x_id0 != 0)) && ((id1 != 0) == (_x_id1 != 0))) && ((id2 != 0) == (_x_id2 != 0))) && (proposed3 == _x_proposed3))) && (max_prop == _x_p3_saved_max)) || ( !((( !(p3_l0 != 0)) && ( !(p3_l1 != 0))) && (((turn0 != 0) && (turn1 != 0)) && (delta == 0.0)))))) && (((max_prop == _x_p3_saved_max) && ((((_x_p3_l0 != 0) && ( !(_x_p3_l1 != 0))) && (_x_p3_x == 0.0)) && ((( !(_x_id2 != 0)) && ((_x_id0 != 0) && (_x_id1 != 0))) && (proposed3 == _x_proposed3)))) || ( !(((p3_l1 != 0) && ( !(p3_l0 != 0))) && (((turn0 != 0) && (turn1 != 0)) && (delta == 0.0)))))) && (((((((id0 != 0) == (_x_id0 != 0)) && ((id1 != 0) == (_x_id1 != 0))) && ((id2 != 0) == (_x_id2 != 0))) && (proposed3 == _x_proposed3)) && ((max_prop == _x_p3_saved_max) && (((( !(_x_p3_l0 != 0)) && ( !(_x_p3_l1 != 0))) && (_x_p3_x == 0.0)) || (((_x_p3_l0 != 0) && (_x_p3_l1 != 0)) && (p3_x == _x_p3_x))))) || ( !(((p3_l0 != 0) && ( !(p3_l1 != 0))) && (((turn0 != 0) && (turn1 != 0)) && (delta == 0.0)))))) && (((max_prop == _x_p3_saved_max) && (((( !(_x_p3_l0 != 0)) && ( !(_x_p3_l1 != 0))) && (p3_x == _x_p3_x)) && (((_x_id2 != 0) && (( !(_x_id0 != 0)) && ( !(_x_id1 != 0)))) && ( !(proposed3 <= _x_proposed3))))) || ( !(((p3_l0 != 0) && (p3_l1 != 0)) && (((turn0 != 0) && (turn1 != 0)) && (delta == 0.0)))))) && (((((((((((( !(_x_p2_l0 != 0)) && ( !(_x_p2_l1 != 0))) || ((_x_p2_l0 != 0) && ( !(_x_p2_l1 != 0)))) || (((_x_p2_l1 != 0) && ( !(_x_p2_l0 != 0))) || ((_x_p2_l0 != 0) && (_x_p2_l1 != 0)))) && ( !(_x_proposed2 <= 0.0))) && ((_x_p2_x <= _x_proposed2) || ( !((_x_p2_l1 != 0) && ( !(_x_p2_l0 != 0)))))) && ((((((p2_l0 != 0) == (_x_p2_l0 != 0)) && ((p2_l1 != 0) == (_x_p2_l1 != 0))) && ((delta + (p2_x + (-1.0 * _x_p2_x))) == 0.0)) && ((p2_saved_max == _x_p2_saved_max) && (proposed2 == _x_proposed2))) || ( !(( !(delta <= 0.0)) || ( !((turn1 != 0) && ( !(turn0 != 0)))))))) && ((((((_x_p2_l1 != 0) && ( !(_x_p2_l0 != 0))) && (_x_p2_x == 0.0)) && (((((id0 != 0) == (_x_id0 != 0)) && ((id1 != 0) == (_x_id1 != 0))) && ((id2 != 0) == (_x_id2 != 0))) && (proposed2 == _x_proposed2))) && (max_prop == _x_p2_saved_max)) || ( !((( !(p2_l0 != 0)) && ( !(p2_l1 != 0))) && (((turn1 != 0) && ( !(turn0 != 0))) && (delta == 0.0)))))) && (((max_prop == _x_p2_saved_max) && ((((_x_p2_l0 != 0) && ( !(_x_p2_l1 != 0))) && (_x_p2_x == 0.0)) && ((( !(_x_id2 != 0)) && ((_x_id1 != 0) && ( !(_x_id0 != 0)))) && (proposed2 == _x_proposed2)))) || ( !(((p2_l1 != 0) && ( !(p2_l0 != 0))) && (((turn1 != 0) && ( !(turn0 != 0))) && (delta == 0.0)))))) && (((((((id0 != 0) == (_x_id0 != 0)) && ((id1 != 0) == (_x_id1 != 0))) && ((id2 != 0) == (_x_id2 != 0))) && (proposed2 == _x_proposed2)) && ((max_prop == _x_p2_saved_max) && (((( !(_x_p2_l0 != 0)) && ( !(_x_p2_l1 != 0))) && (_x_p2_x == 0.0)) || (((_x_p2_l0 != 0) && (_x_p2_l1 != 0)) && (p2_x == _x_p2_x))))) || ( !(((p2_l0 != 0) && ( !(p2_l1 != 0))) && (((turn1 != 0) && ( !(turn0 != 0))) && (delta == 0.0)))))) && (((max_prop == _x_p2_saved_max) && (((( !(_x_p2_l0 != 0)) && ( !(_x_p2_l1 != 0))) && (p2_x == _x_p2_x)) && (((_x_id2 != 0) && (( !(_x_id0 != 0)) && ( !(_x_id1 != 0)))) && ( !(proposed2 <= _x_proposed2))))) || ( !(((p2_l0 != 0) && (p2_l1 != 0)) && (((turn1 != 0) && ( !(turn0 != 0))) && (delta == 0.0)))))) && (((((((((((( !(_x_p1_l0 != 0)) && ( !(_x_p1_l1 != 0))) || ((_x_p1_l0 != 0) && ( !(_x_p1_l1 != 0)))) || (((_x_p1_l1 != 0) && ( !(_x_p1_l0 != 0))) || ((_x_p1_l0 != 0) && (_x_p1_l1 != 0)))) && ( !(_x_proposed1 <= 0.0))) && ((_x_p1_x <= _x_proposed1) || ( !((_x_p1_l1 != 0) && ( !(_x_p1_l0 != 0)))))) && ((((((p1_l0 != 0) == (_x_p1_l0 != 0)) && ((p1_l1 != 0) == (_x_p1_l1 != 0))) && ((delta + (p1_x + (-1.0 * _x_p1_x))) == 0.0)) && ((p1_saved_max == _x_p1_saved_max) && (proposed1 == _x_proposed1))) || ( !(( !(delta <= 0.0)) || ( !((turn0 != 0) && ( !(turn1 != 0)))))))) && ((((((_x_p1_l1 != 0) && ( !(_x_p1_l0 != 0))) && (_x_p1_x == 0.0)) && (((((id0 != 0) == (_x_id0 != 0)) && ((id1 != 0) == (_x_id1 != 0))) && ((id2 != 0) == (_x_id2 != 0))) && (proposed1 == _x_proposed1))) && (max_prop == _x_p1_saved_max)) || ( !((( !(p1_l0 != 0)) && ( !(p1_l1 != 0))) && (((turn0 != 0) && ( !(turn1 != 0))) && (delta == 0.0)))))) && (((max_prop == _x_p1_saved_max) && ((((_x_p1_l0 != 0) && ( !(_x_p1_l1 != 0))) && (_x_p1_x == 0.0)) && ((( !(_x_id2 != 0)) && ((_x_id0 != 0) && ( !(_x_id1 != 0)))) && (proposed1 == _x_proposed1)))) || ( !(((p1_l1 != 0) && ( !(p1_l0 != 0))) && (((turn0 != 0) && ( !(turn1 != 0))) && (delta == 0.0)))))) && (((((((id0 != 0) == (_x_id0 != 0)) && ((id1 != 0) == (_x_id1 != 0))) && ((id2 != 0) == (_x_id2 != 0))) && (proposed1 == _x_proposed1)) && ((max_prop == _x_p1_saved_max) && (((( !(_x_p1_l0 != 0)) && ( !(_x_p1_l1 != 0))) && (_x_p1_x == 0.0)) || (((_x_p1_l0 != 0) && (_x_p1_l1 != 0)) && (p1_x == _x_p1_x))))) || ( !(((p1_l0 != 0) && ( !(p1_l1 != 0))) && (((turn0 != 0) && ( !(turn1 != 0))) && (delta == 0.0)))))) && (((max_prop == _x_p1_saved_max) && (((( !(_x_p1_l0 != 0)) && ( !(_x_p1_l1 != 0))) && (p1_x == _x_p1_x)) && (((_x_id2 != 0) && (( !(_x_id0 != 0)) && ( !(_x_id1 != 0)))) && ( !(proposed1 <= _x_proposed1))))) || ( !(((p1_l0 != 0) && (p1_l1 != 0)) && (((turn0 != 0) && ( !(turn1 != 0))) && (delta == 0.0)))))) && (((((((((((( !(_x_p0_l0 != 0)) && ( !(_x_p0_l1 != 0))) || ((_x_p0_l0 != 0) && ( !(_x_p0_l1 != 0)))) || (((_x_p0_l1 != 0) && ( !(_x_p0_l0 != 0))) || ((_x_p0_l0 != 0) && (_x_p0_l1 != 0)))) && ( !(_x_proposed0 <= 0.0))) && ((_x_p0_x <= _x_proposed0) || ( !((_x_p0_l1 != 0) && ( !(_x_p0_l0 != 0)))))) && ((((((p0_l0 != 0) == (_x_p0_l0 != 0)) && ((p0_l1 != 0) == (_x_p0_l1 != 0))) && ((delta + (p0_x + (-1.0 * _x_p0_x))) == 0.0)) && ((p0_saved_max == _x_p0_saved_max) && (proposed0 == _x_proposed0))) || ( !(( !(delta <= 0.0)) || ( !(( !(turn0 != 0)) && ( !(turn1 != 0)))))))) && ((((((_x_p0_l1 != 0) && ( !(_x_p0_l0 != 0))) && (_x_p0_x == 0.0)) && (((((id0 != 0) == (_x_id0 != 0)) && ((id1 != 0) == (_x_id1 != 0))) && ((id2 != 0) == (_x_id2 != 0))) && (proposed0 == _x_proposed0))) && (max_prop == _x_p0_saved_max)) || ( !((( !(p0_l0 != 0)) && ( !(p0_l1 != 0))) && ((( !(turn0 != 0)) && ( !(turn1 != 0))) && (delta == 0.0)))))) && (((max_prop == _x_p0_saved_max) && ((((_x_p0_l0 != 0) && ( !(_x_p0_l1 != 0))) && (_x_p0_x == 0.0)) && ((( !(_x_id2 != 0)) && (( !(_x_id0 != 0)) && ( !(_x_id1 != 0)))) && (proposed0 == _x_proposed0)))) || ( !(((p0_l1 != 0) && ( !(p0_l0 != 0))) && ((( !(turn0 != 0)) && ( !(turn1 != 0))) && (delta == 0.0)))))) && (((((((id0 != 0) == (_x_id0 != 0)) && ((id1 != 0) == (_x_id1 != 0))) && ((id2 != 0) == (_x_id2 != 0))) && (proposed0 == _x_proposed0)) && ((max_prop == _x_p0_saved_max) && (((( !(_x_p0_l0 != 0)) && ( !(_x_p0_l1 != 0))) && (_x_p0_x == 0.0)) || (((_x_p0_l0 != 0) && (_x_p0_l1 != 0)) && (p0_x == _x_p0_x))))) || ( !(((p0_l0 != 0) && ( !(p0_l1 != 0))) && ((( !(turn0 != 0)) && ( !(turn1 != 0))) && (delta == 0.0)))))) && (((max_prop == _x_p0_saved_max) && (((( !(_x_p0_l0 != 0)) && ( !(_x_p0_l1 != 0))) && (p0_x == _x_p0_x)) && (((_x_id2 != 0) && (( !(_x_id0 != 0)) && ( !(_x_id1 != 0)))) && ( !(proposed0 <= _x_proposed0))))) || ( !(((p0_l0 != 0) && (p0_l1 != 0)) && ((( !(turn0 != 0)) && ( !(turn1 != 0))) && (delta == 0.0)))))) && ((((((((((((_x_id2 != 0) && (( !(_x_id0 != 0)) && ( !(_x_id1 != 0)))) || ((( !(_x_id2 != 0)) && ((_x_id0 != 0) && (_x_id1 != 0))) || ((( !(_x_id2 != 0)) && ((_x_id1 != 0) && ( !(_x_id0 != 0)))) || ((( !(_x_id2 != 0)) && (( !(_x_id0 != 0)) && ( !(_x_id1 != 0)))) || (( !(_x_id2 != 0)) && ((_x_id0 != 0) && ( !(_x_id1 != 0)))))))) && (((_x_turn0 != 0) && (_x_turn1 != 0)) || (((_x_turn1 != 0) && ( !(_x_turn0 != 0))) || ((( !(_x_turn0 != 0)) && ( !(_x_turn1 != 0))) || ((_x_turn0 != 0) && ( !(_x_turn1 != 0))))))) && ((delta <= 0.0) || ((_x_inc_max_prop != 0) && (((((id0 != 0) == (_x_id0 != 0)) && ((id1 != 0) == (_x_id1 != 0))) && ((id2 != 0) == (_x_id2 != 0))) && (((turn0 != 0) == (_x_turn0 != 0)) && ((turn1 != 0) == (_x_turn1 != 0))))))) && (0.0 <= _x_delta)) && (_x_proposed0 <= _x_max_prop)) && (_x_proposed1 <= _x_max_prop)) && (_x_proposed2 <= _x_max_prop)) && (_x_proposed3 <= _x_max_prop)) && ((((_x_proposed0 == _x_max_prop) || (_x_proposed1 == _x_max_prop)) || (_x_proposed2 == _x_max_prop)) || (_x_proposed3 == _x_max_prop))) && ((_x_inc_max_prop != 0) == (max_prop <= _x_max_prop))))))) && (((delta == _x__diverge_delta) || ( !(1.0 <= _diverge_delta))) && ((1.0 <= _diverge_delta) || ((delta + (_diverge_delta + (-1.0 * _x__diverge_delta))) == 0.0))));
    p3_saved_max = _x_p3_saved_max;
    p3_x = _x_p3_x;
    p2_l1 = _x_p2_l1;
    p2_l0 = _x_p2_l0;
    p2_saved_max = _x_p2_saved_max;
    p0_l1 = _x_p0_l1;
    p0_l0 = _x_p0_l0;
    p0_saved_max = _x_p0_saved_max;
    max_prop = _x_max_prop;
    p3_l0 = _x_p3_l0;
    id1 = _x_id1;
    delta = _x_delta;
    p3_l1 = _x_p3_l1;
    id2 = _x_id2;
    _diverge_delta = _x__diverge_delta;
    p1_l0 = _x_p1_l0;
    turn0 = _x_turn0;
    p2_x = _x_p2_x;
    p1_l1 = _x_p1_l1;
    turn1 = _x_turn1;
    p0_x = _x_p0_x;
    inc_max_prop = _x_inc_max_prop;
    id0 = _x_id0;
    proposed3 = _x_proposed3;
    p1_x = _x_p1_x;
    proposed0 = _x_proposed0;
    p1_saved_max = _x_p1_saved_max;
    proposed1 = _x_proposed1;
    proposed2 = _x_proposed2;

  }
}
