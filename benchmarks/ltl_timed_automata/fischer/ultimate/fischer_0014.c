//@ ltl invariant negative: ( ( ([] (<> ( AP((p0_l0 != 0)) && AP((p0_l1 != 0))))) || (! ([] (<> ( AP((p0_l0 != 0)) && (! AP((p0_l1 != 0)))))))) || (! ([] (<> AP((1.0 <= _diverge_delta))))));

extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);

char __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}


float _diverge_delta, _x__diverge_delta;
char p12_l0, _x_p12_l0;
float p12_x, _x_p12_x;
char p11_l0, _x_p11_l0;
float p11_x, _x_p11_x;
char p10_l0, _x_p10_l0;
float p10_x, _x_p10_x;
float p9_x, _x_p9_x;
char p2_l1, _x_p2_l1;
float p6_x, _x_p6_x;
char p8_l1, _x_p8_l1;
char p2_l0, _x_p2_l0;
char p13_l0, _x_p13_l0;
float p2_x, _x_p2_x;
char p1_l1, _x_p1_l1;
float delta, _x_delta;
float p13_x, _x_p13_x;
char p0_l0, _x_p0_l0;
char p7_l1, _x_p7_l1;
float p0_x, _x_p0_x;
char p12_l1, _x_p12_l1;
char p6_l0, _x_p6_l0;
int turn, _x_turn;
int id, _x_id;
float p3_x, _x_p3_x;
char p9_l0, _x_p9_l0;
float p1_x, _x_p1_x;
char p5_l1, _x_p5_l1;
char p9_l1, _x_p9_l1;
char p3_l0, _x_p3_l0;
char p3_l1, _x_p3_l1;
char p0_l1, _x_p0_l1;
float p7_x, _x_p7_x;
float p4_x, _x_p4_x;
char p10_l1, _x_p10_l1;
char p4_l0, _x_p4_l0;
char p1_l0, _x_p1_l0;
char p4_l1, _x_p4_l1;
float p8_x, _x_p8_x;
float p5_x, _x_p5_x;
char p11_l1, _x_p11_l1;
char p5_l0, _x_p5_l0;
char p6_l1, _x_p6_l1;
char p13_l1, _x_p13_l1;
char p7_l0, _x_p7_l0;
char p8_l0, _x_p8_l0;

int main()
{
  _diverge_delta = __VERIFIER_nondet_float();
  p12_l0 = __VERIFIER_nondet_bool();
  p12_x = __VERIFIER_nondet_float();
  p11_l0 = __VERIFIER_nondet_bool();
  p11_x = __VERIFIER_nondet_float();
  p10_l0 = __VERIFIER_nondet_bool();
  p10_x = __VERIFIER_nondet_float();
  p9_x = __VERIFIER_nondet_float();
  p2_l1 = __VERIFIER_nondet_bool();
  p6_x = __VERIFIER_nondet_float();
  p8_l1 = __VERIFIER_nondet_bool();
  p2_l0 = __VERIFIER_nondet_bool();
  p13_l0 = __VERIFIER_nondet_bool();
  p2_x = __VERIFIER_nondet_float();
  p1_l1 = __VERIFIER_nondet_bool();
  delta = __VERIFIER_nondet_float();
  p13_x = __VERIFIER_nondet_float();
  p0_l0 = __VERIFIER_nondet_bool();
  p7_l1 = __VERIFIER_nondet_bool();
  p0_x = __VERIFIER_nondet_float();
  p12_l1 = __VERIFIER_nondet_bool();
  p6_l0 = __VERIFIER_nondet_bool();
  turn = __VERIFIER_nondet_int();
  id = __VERIFIER_nondet_int();
  p3_x = __VERIFIER_nondet_float();
  p9_l0 = __VERIFIER_nondet_bool();
  p1_x = __VERIFIER_nondet_float();
  p5_l1 = __VERIFIER_nondet_bool();
  p9_l1 = __VERIFIER_nondet_bool();
  p3_l0 = __VERIFIER_nondet_bool();
  p3_l1 = __VERIFIER_nondet_bool();
  p0_l1 = __VERIFIER_nondet_bool();
  p7_x = __VERIFIER_nondet_float();
  p4_x = __VERIFIER_nondet_float();
  p10_l1 = __VERIFIER_nondet_bool();
  p4_l0 = __VERIFIER_nondet_bool();
  p1_l0 = __VERIFIER_nondet_bool();
  p4_l1 = __VERIFIER_nondet_bool();
  p8_x = __VERIFIER_nondet_float();
  p5_x = __VERIFIER_nondet_float();
  p11_l1 = __VERIFIER_nondet_bool();
  p5_l0 = __VERIFIER_nondet_bool();
  p6_l1 = __VERIFIER_nondet_bool();
  p13_l1 = __VERIFIER_nondet_bool();
  p7_l0 = __VERIFIER_nondet_bool();
  p8_l0 = __VERIFIER_nondet_bool();

  int __ok = (((id == 0) && (((((( !(p13_l0 != 0)) && ( !(p13_l1 != 0))) && (p13_x == 0.0)) && (((( !(p13_l0 != 0)) && ( !(p13_l1 != 0))) || ((p13_l0 != 0) && ( !(p13_l1 != 0)))) || (((p13_l1 != 0) && ( !(p13_l0 != 0))) || ((p13_l0 != 0) && (p13_l1 != 0))))) && ((p13_x <= 2.0) || ( !((p13_l1 != 0) && ( !(p13_l0 != 0)))))) && (((((( !(p12_l0 != 0)) && ( !(p12_l1 != 0))) && (p12_x == 0.0)) && (((( !(p12_l0 != 0)) && ( !(p12_l1 != 0))) || ((p12_l0 != 0) && ( !(p12_l1 != 0)))) || (((p12_l1 != 0) && ( !(p12_l0 != 0))) || ((p12_l0 != 0) && (p12_l1 != 0))))) && ((p12_x <= 2.0) || ( !((p12_l1 != 0) && ( !(p12_l0 != 0)))))) && (((((( !(p11_l0 != 0)) && ( !(p11_l1 != 0))) && (p11_x == 0.0)) && (((( !(p11_l0 != 0)) && ( !(p11_l1 != 0))) || ((p11_l0 != 0) && ( !(p11_l1 != 0)))) || (((p11_l1 != 0) && ( !(p11_l0 != 0))) || ((p11_l0 != 0) && (p11_l1 != 0))))) && ((p11_x <= 2.0) || ( !((p11_l1 != 0) && ( !(p11_l0 != 0)))))) && (((((( !(p10_l0 != 0)) && ( !(p10_l1 != 0))) && (p10_x == 0.0)) && (((( !(p10_l0 != 0)) && ( !(p10_l1 != 0))) || ((p10_l0 != 0) && ( !(p10_l1 != 0)))) || (((p10_l1 != 0) && ( !(p10_l0 != 0))) || ((p10_l0 != 0) && (p10_l1 != 0))))) && ((p10_x <= 2.0) || ( !((p10_l1 != 0) && ( !(p10_l0 != 0)))))) && (((((( !(p9_l0 != 0)) && ( !(p9_l1 != 0))) && (p9_x == 0.0)) && (((( !(p9_l0 != 0)) && ( !(p9_l1 != 0))) || ((p9_l0 != 0) && ( !(p9_l1 != 0)))) || (((p9_l1 != 0) && ( !(p9_l0 != 0))) || ((p9_l0 != 0) && (p9_l1 != 0))))) && ((p9_x <= 2.0) || ( !((p9_l1 != 0) && ( !(p9_l0 != 0)))))) && (((((( !(p8_l0 != 0)) && ( !(p8_l1 != 0))) && (p8_x == 0.0)) && (((( !(p8_l0 != 0)) && ( !(p8_l1 != 0))) || ((p8_l0 != 0) && ( !(p8_l1 != 0)))) || (((p8_l1 != 0) && ( !(p8_l0 != 0))) || ((p8_l0 != 0) && (p8_l1 != 0))))) && ((p8_x <= 2.0) || ( !((p8_l1 != 0) && ( !(p8_l0 != 0)))))) && (((((( !(p7_l0 != 0)) && ( !(p7_l1 != 0))) && (p7_x == 0.0)) && (((( !(p7_l0 != 0)) && ( !(p7_l1 != 0))) || ((p7_l0 != 0) && ( !(p7_l1 != 0)))) || (((p7_l1 != 0) && ( !(p7_l0 != 0))) || ((p7_l0 != 0) && (p7_l1 != 0))))) && ((p7_x <= 2.0) || ( !((p7_l1 != 0) && ( !(p7_l0 != 0)))))) && (((((( !(p6_l0 != 0)) && ( !(p6_l1 != 0))) && (p6_x == 0.0)) && (((( !(p6_l0 != 0)) && ( !(p6_l1 != 0))) || ((p6_l0 != 0) && ( !(p6_l1 != 0)))) || (((p6_l1 != 0) && ( !(p6_l0 != 0))) || ((p6_l0 != 0) && (p6_l1 != 0))))) && ((p6_x <= 2.0) || ( !((p6_l1 != 0) && ( !(p6_l0 != 0)))))) && (((((( !(p5_l0 != 0)) && ( !(p5_l1 != 0))) && (p5_x == 0.0)) && (((( !(p5_l0 != 0)) && ( !(p5_l1 != 0))) || ((p5_l0 != 0) && ( !(p5_l1 != 0)))) || (((p5_l1 != 0) && ( !(p5_l0 != 0))) || ((p5_l0 != 0) && (p5_l1 != 0))))) && ((p5_x <= 2.0) || ( !((p5_l1 != 0) && ( !(p5_l0 != 0)))))) && (((((( !(p4_l0 != 0)) && ( !(p4_l1 != 0))) && (p4_x == 0.0)) && (((( !(p4_l0 != 0)) && ( !(p4_l1 != 0))) || ((p4_l0 != 0) && ( !(p4_l1 != 0)))) || (((p4_l1 != 0) && ( !(p4_l0 != 0))) || ((p4_l0 != 0) && (p4_l1 != 0))))) && ((p4_x <= 2.0) || ( !((p4_l1 != 0) && ( !(p4_l0 != 0)))))) && (((((( !(p3_l0 != 0)) && ( !(p3_l1 != 0))) && (p3_x == 0.0)) && (((( !(p3_l0 != 0)) && ( !(p3_l1 != 0))) || ((p3_l0 != 0) && ( !(p3_l1 != 0)))) || (((p3_l1 != 0) && ( !(p3_l0 != 0))) || ((p3_l0 != 0) && (p3_l1 != 0))))) && ((p3_x <= 2.0) || ( !((p3_l1 != 0) && ( !(p3_l0 != 0)))))) && (((((( !(p2_l0 != 0)) && ( !(p2_l1 != 0))) && (p2_x == 0.0)) && (((( !(p2_l0 != 0)) && ( !(p2_l1 != 0))) || ((p2_l0 != 0) && ( !(p2_l1 != 0)))) || (((p2_l1 != 0) && ( !(p2_l0 != 0))) || ((p2_l0 != 0) && (p2_l1 != 0))))) && ((p2_x <= 2.0) || ( !((p2_l1 != 0) && ( !(p2_l0 != 0)))))) && (((((( !(p1_l0 != 0)) && ( !(p1_l1 != 0))) && (p1_x == 0.0)) && (((( !(p1_l0 != 0)) && ( !(p1_l1 != 0))) || ((p1_l0 != 0) && ( !(p1_l1 != 0)))) || (((p1_l1 != 0) && ( !(p1_l0 != 0))) || ((p1_l0 != 0) && (p1_l1 != 0))))) && ((p1_x <= 2.0) || ( !((p1_l1 != 0) && ( !(p1_l0 != 0)))))) && (((((( !(p0_l0 != 0)) && ( !(p0_l1 != 0))) && (p0_x == 0.0)) && (((( !(p0_l0 != 0)) && ( !(p0_l1 != 0))) || ((p0_l0 != 0) && ( !(p0_l1 != 0)))) || (((p0_l1 != 0) && ( !(p0_l0 != 0))) || ((p0_l0 != 0) && (p0_l1 != 0))))) && ((p0_x <= 2.0) || ( !((p0_l1 != 0) && ( !(p0_l0 != 0)))))) && (((0.0 <= delta) && ((id == 14) || ((id == 13) || ((id == 12) || ((id == 11) || ((id == 10) || ((id == 9) || ((id == 8) || ((id == 7) || ((id == 6) || ((id == 5) || ((id == 4) || ((id == 3) || ((id == 2) || ((id == 0) || (id == 1)))))))))))))))) && ((turn == 14) || ((turn == 13) || ((turn == 12) || ((turn == 11) || ((turn == 10) || ((turn == 9) || ((turn == 8) || ((turn == 7) || ((turn == 6) || ((turn == 5) || ((turn == 4) || ((turn == 3) || ((turn == 1) || (turn == 2)))))))))))))))))))))))))))))) && (delta == _diverge_delta));
  while (__ok) {
    _x__diverge_delta = __VERIFIER_nondet_float();
    _x_p12_l0 = __VERIFIER_nondet_bool();
    _x_p12_x = __VERIFIER_nondet_float();
    _x_p11_l0 = __VERIFIER_nondet_bool();
    _x_p11_x = __VERIFIER_nondet_float();
    _x_p10_l0 = __VERIFIER_nondet_bool();
    _x_p10_x = __VERIFIER_nondet_float();
    _x_p9_x = __VERIFIER_nondet_float();
    _x_p2_l1 = __VERIFIER_nondet_bool();
    _x_p6_x = __VERIFIER_nondet_float();
    _x_p8_l1 = __VERIFIER_nondet_bool();
    _x_p2_l0 = __VERIFIER_nondet_bool();
    _x_p13_l0 = __VERIFIER_nondet_bool();
    _x_p2_x = __VERIFIER_nondet_float();
    _x_p1_l1 = __VERIFIER_nondet_bool();
    _x_delta = __VERIFIER_nondet_float();
    _x_p13_x = __VERIFIER_nondet_float();
    _x_p0_l0 = __VERIFIER_nondet_bool();
    _x_p7_l1 = __VERIFIER_nondet_bool();
    _x_p0_x = __VERIFIER_nondet_float();
    _x_p12_l1 = __VERIFIER_nondet_bool();
    _x_p6_l0 = __VERIFIER_nondet_bool();
    _x_turn = __VERIFIER_nondet_int();
    _x_id = __VERIFIER_nondet_int();
    _x_p3_x = __VERIFIER_nondet_float();
    _x_p9_l0 = __VERIFIER_nondet_bool();
    _x_p1_x = __VERIFIER_nondet_float();
    _x_p5_l1 = __VERIFIER_nondet_bool();
    _x_p9_l1 = __VERIFIER_nondet_bool();
    _x_p3_l0 = __VERIFIER_nondet_bool();
    _x_p3_l1 = __VERIFIER_nondet_bool();
    _x_p0_l1 = __VERIFIER_nondet_bool();
    _x_p7_x = __VERIFIER_nondet_float();
    _x_p4_x = __VERIFIER_nondet_float();
    _x_p10_l1 = __VERIFIER_nondet_bool();
    _x_p4_l0 = __VERIFIER_nondet_bool();
    _x_p1_l0 = __VERIFIER_nondet_bool();
    _x_p4_l1 = __VERIFIER_nondet_bool();
    _x_p8_x = __VERIFIER_nondet_float();
    _x_p5_x = __VERIFIER_nondet_float();
    _x_p11_l1 = __VERIFIER_nondet_bool();
    _x_p5_l0 = __VERIFIER_nondet_bool();
    _x_p6_l1 = __VERIFIER_nondet_bool();
    _x_p13_l1 = __VERIFIER_nondet_bool();
    _x_p7_l0 = __VERIFIER_nondet_bool();
    _x_p8_l0 = __VERIFIER_nondet_bool();

    __ok = (((((((((((((( !(_x_p13_l0 != 0)) && ( !(_x_p13_l1 != 0))) || ((_x_p13_l0 != 0) && ( !(_x_p13_l1 != 0)))) || (((_x_p13_l1 != 0) && ( !(_x_p13_l0 != 0))) || ((_x_p13_l0 != 0) && (_x_p13_l1 != 0)))) && ((_x_p13_x <= 2.0) || ( !((_x_p13_l1 != 0) && ( !(_x_p13_l0 != 0)))))) && (((((p13_l0 != 0) == (_x_p13_l0 != 0)) && ((p13_l1 != 0) == (_x_p13_l1 != 0))) && ((delta + (p13_x + (-1.0 * _x_p13_x))) == 0.0)) || ( !(( !(delta <= 0.0)) || ( !(turn == 14)))))) && ((((id == 0) && ((_x_p13_l1 != 0) && ( !(_x_p13_l0 != 0)))) && ((id == _x_id) && (_x_p13_x == 0.0))) || ( !((( !(p13_l0 != 0)) && ( !(p13_l1 != 0))) && ((delta == 0.0) && (turn == 14)))))) && (((((_x_p13_l0 != 0) && ( !(_x_p13_l1 != 0))) && (p13_x <= 2.0)) && ((_x_p13_x == 0.0) && (_x_id == 14))) || ( !(((p13_l1 != 0) && ( !(p13_l0 != 0))) && ((delta == 0.0) && (turn == 14)))))) && (((( !(_x_p13_l0 != 0)) && ( !(_x_p13_l1 != 0))) || ((_x_p13_l0 != 0) && (_x_p13_l1 != 0))) || ( !(((p13_l0 != 0) && ( !(p13_l1 != 0))) && ((delta == 0.0) && (turn == 14)))))) && ((((id == _x_id) && (_x_p13_x == 0.0)) && (( !(p13_x <= 2.0)) && ( !(id == 14)))) || ( !(((delta == 0.0) && (turn == 14)) && ((( !(_x_p13_l0 != 0)) && ( !(_x_p13_l1 != 0))) && ((p13_l0 != 0) && ( !(p13_l1 != 0)))))))) && ((((id == _x_id) && (p13_x == _x_p13_x)) && (( !(p13_x <= 2.0)) && (id == 14))) || ( !(((delta == 0.0) && (turn == 14)) && (((p13_l0 != 0) && ( !(p13_l1 != 0))) && ((_x_p13_l0 != 0) && (_x_p13_l1 != 0))))))) && (((( !(_x_p13_l0 != 0)) && ( !(_x_p13_l1 != 0))) && ((_x_id == 0) && (p13_x == _x_p13_x))) || ( !(((p13_l0 != 0) && (p13_l1 != 0)) && ((delta == 0.0) && (turn == 14)))))) && ((((((((((((( !(_x_p12_l0 != 0)) && ( !(_x_p12_l1 != 0))) || ((_x_p12_l0 != 0) && ( !(_x_p12_l1 != 0)))) || (((_x_p12_l1 != 0) && ( !(_x_p12_l0 != 0))) || ((_x_p12_l0 != 0) && (_x_p12_l1 != 0)))) && ((_x_p12_x <= 2.0) || ( !((_x_p12_l1 != 0) && ( !(_x_p12_l0 != 0)))))) && (((((p12_l0 != 0) == (_x_p12_l0 != 0)) && ((p12_l1 != 0) == (_x_p12_l1 != 0))) && ((delta + (p12_x + (-1.0 * _x_p12_x))) == 0.0)) || ( !(( !(delta <= 0.0)) || ( !(turn == 13)))))) && ((((id == 0) && ((_x_p12_l1 != 0) && ( !(_x_p12_l0 != 0)))) && ((id == _x_id) && (_x_p12_x == 0.0))) || ( !((( !(p12_l0 != 0)) && ( !(p12_l1 != 0))) && ((delta == 0.0) && (turn == 13)))))) && (((((_x_p12_l0 != 0) && ( !(_x_p12_l1 != 0))) && (p12_x <= 2.0)) && ((_x_p12_x == 0.0) && (_x_id == 13))) || ( !(((p12_l1 != 0) && ( !(p12_l0 != 0))) && ((delta == 0.0) && (turn == 13)))))) && (((( !(_x_p12_l0 != 0)) && ( !(_x_p12_l1 != 0))) || ((_x_p12_l0 != 0) && (_x_p12_l1 != 0))) || ( !(((p12_l0 != 0) && ( !(p12_l1 != 0))) && ((delta == 0.0) && (turn == 13)))))) && ((((id == _x_id) && (_x_p12_x == 0.0)) && (( !(p12_x <= 2.0)) && ( !(id == 13)))) || ( !(((delta == 0.0) && (turn == 13)) && ((( !(_x_p12_l0 != 0)) && ( !(_x_p12_l1 != 0))) && ((p12_l0 != 0) && ( !(p12_l1 != 0)))))))) && ((((id == _x_id) && (p12_x == _x_p12_x)) && (( !(p12_x <= 2.0)) && (id == 13))) || ( !(((delta == 0.0) && (turn == 13)) && (((p12_l0 != 0) && ( !(p12_l1 != 0))) && ((_x_p12_l0 != 0) && (_x_p12_l1 != 0))))))) && (((( !(_x_p12_l0 != 0)) && ( !(_x_p12_l1 != 0))) && ((_x_id == 0) && (p12_x == _x_p12_x))) || ( !(((p12_l0 != 0) && (p12_l1 != 0)) && ((delta == 0.0) && (turn == 13)))))) && ((((((((((((( !(_x_p11_l0 != 0)) && ( !(_x_p11_l1 != 0))) || ((_x_p11_l0 != 0) && ( !(_x_p11_l1 != 0)))) || (((_x_p11_l1 != 0) && ( !(_x_p11_l0 != 0))) || ((_x_p11_l0 != 0) && (_x_p11_l1 != 0)))) && ((_x_p11_x <= 2.0) || ( !((_x_p11_l1 != 0) && ( !(_x_p11_l0 != 0)))))) && (((((p11_l0 != 0) == (_x_p11_l0 != 0)) && ((p11_l1 != 0) == (_x_p11_l1 != 0))) && ((delta + (p11_x + (-1.0 * _x_p11_x))) == 0.0)) || ( !(( !(delta <= 0.0)) || ( !(turn == 12)))))) && ((((id == 0) && ((_x_p11_l1 != 0) && ( !(_x_p11_l0 != 0)))) && ((id == _x_id) && (_x_p11_x == 0.0))) || ( !((( !(p11_l0 != 0)) && ( !(p11_l1 != 0))) && ((delta == 0.0) && (turn == 12)))))) && (((((_x_p11_l0 != 0) && ( !(_x_p11_l1 != 0))) && (p11_x <= 2.0)) && ((_x_p11_x == 0.0) && (_x_id == 12))) || ( !(((p11_l1 != 0) && ( !(p11_l0 != 0))) && ((delta == 0.0) && (turn == 12)))))) && (((( !(_x_p11_l0 != 0)) && ( !(_x_p11_l1 != 0))) || ((_x_p11_l0 != 0) && (_x_p11_l1 != 0))) || ( !(((p11_l0 != 0) && ( !(p11_l1 != 0))) && ((delta == 0.0) && (turn == 12)))))) && ((((id == _x_id) && (_x_p11_x == 0.0)) && (( !(p11_x <= 2.0)) && ( !(id == 12)))) || ( !(((delta == 0.0) && (turn == 12)) && ((( !(_x_p11_l0 != 0)) && ( !(_x_p11_l1 != 0))) && ((p11_l0 != 0) && ( !(p11_l1 != 0)))))))) && ((((id == _x_id) && (p11_x == _x_p11_x)) && (( !(p11_x <= 2.0)) && (id == 12))) || ( !(((delta == 0.0) && (turn == 12)) && (((p11_l0 != 0) && ( !(p11_l1 != 0))) && ((_x_p11_l0 != 0) && (_x_p11_l1 != 0))))))) && (((( !(_x_p11_l0 != 0)) && ( !(_x_p11_l1 != 0))) && ((_x_id == 0) && (p11_x == _x_p11_x))) || ( !(((p11_l0 != 0) && (p11_l1 != 0)) && ((delta == 0.0) && (turn == 12)))))) && ((((((((((((( !(_x_p10_l0 != 0)) && ( !(_x_p10_l1 != 0))) || ((_x_p10_l0 != 0) && ( !(_x_p10_l1 != 0)))) || (((_x_p10_l1 != 0) && ( !(_x_p10_l0 != 0))) || ((_x_p10_l0 != 0) && (_x_p10_l1 != 0)))) && ((_x_p10_x <= 2.0) || ( !((_x_p10_l1 != 0) && ( !(_x_p10_l0 != 0)))))) && (((((p10_l0 != 0) == (_x_p10_l0 != 0)) && ((p10_l1 != 0) == (_x_p10_l1 != 0))) && ((delta + (p10_x + (-1.0 * _x_p10_x))) == 0.0)) || ( !(( !(delta <= 0.0)) || ( !(turn == 11)))))) && ((((id == 0) && ((_x_p10_l1 != 0) && ( !(_x_p10_l0 != 0)))) && ((id == _x_id) && (_x_p10_x == 0.0))) || ( !((( !(p10_l0 != 0)) && ( !(p10_l1 != 0))) && ((delta == 0.0) && (turn == 11)))))) && (((((_x_p10_l0 != 0) && ( !(_x_p10_l1 != 0))) && (p10_x <= 2.0)) && ((_x_p10_x == 0.0) && (_x_id == 11))) || ( !(((p10_l1 != 0) && ( !(p10_l0 != 0))) && ((delta == 0.0) && (turn == 11)))))) && (((( !(_x_p10_l0 != 0)) && ( !(_x_p10_l1 != 0))) || ((_x_p10_l0 != 0) && (_x_p10_l1 != 0))) || ( !(((p10_l0 != 0) && ( !(p10_l1 != 0))) && ((delta == 0.0) && (turn == 11)))))) && ((((id == _x_id) && (_x_p10_x == 0.0)) && (( !(p10_x <= 2.0)) && ( !(id == 11)))) || ( !(((delta == 0.0) && (turn == 11)) && ((( !(_x_p10_l0 != 0)) && ( !(_x_p10_l1 != 0))) && ((p10_l0 != 0) && ( !(p10_l1 != 0)))))))) && ((((id == _x_id) && (p10_x == _x_p10_x)) && (( !(p10_x <= 2.0)) && (id == 11))) || ( !(((delta == 0.0) && (turn == 11)) && (((p10_l0 != 0) && ( !(p10_l1 != 0))) && ((_x_p10_l0 != 0) && (_x_p10_l1 != 0))))))) && (((( !(_x_p10_l0 != 0)) && ( !(_x_p10_l1 != 0))) && ((_x_id == 0) && (p10_x == _x_p10_x))) || ( !(((p10_l0 != 0) && (p10_l1 != 0)) && ((delta == 0.0) && (turn == 11)))))) && ((((((((((((( !(_x_p9_l0 != 0)) && ( !(_x_p9_l1 != 0))) || ((_x_p9_l0 != 0) && ( !(_x_p9_l1 != 0)))) || (((_x_p9_l1 != 0) && ( !(_x_p9_l0 != 0))) || ((_x_p9_l0 != 0) && (_x_p9_l1 != 0)))) && ((_x_p9_x <= 2.0) || ( !((_x_p9_l1 != 0) && ( !(_x_p9_l0 != 0)))))) && (((((p9_l0 != 0) == (_x_p9_l0 != 0)) && ((p9_l1 != 0) == (_x_p9_l1 != 0))) && ((delta + (p9_x + (-1.0 * _x_p9_x))) == 0.0)) || ( !(( !(delta <= 0.0)) || ( !(turn == 10)))))) && ((((id == 0) && ((_x_p9_l1 != 0) && ( !(_x_p9_l0 != 0)))) && ((id == _x_id) && (_x_p9_x == 0.0))) || ( !((( !(p9_l0 != 0)) && ( !(p9_l1 != 0))) && ((delta == 0.0) && (turn == 10)))))) && (((((_x_p9_l0 != 0) && ( !(_x_p9_l1 != 0))) && (p9_x <= 2.0)) && ((_x_p9_x == 0.0) && (_x_id == 10))) || ( !(((p9_l1 != 0) && ( !(p9_l0 != 0))) && ((delta == 0.0) && (turn == 10)))))) && (((( !(_x_p9_l0 != 0)) && ( !(_x_p9_l1 != 0))) || ((_x_p9_l0 != 0) && (_x_p9_l1 != 0))) || ( !(((p9_l0 != 0) && ( !(p9_l1 != 0))) && ((delta == 0.0) && (turn == 10)))))) && ((((id == _x_id) && (_x_p9_x == 0.0)) && (( !(p9_x <= 2.0)) && ( !(id == 10)))) || ( !(((delta == 0.0) && (turn == 10)) && ((( !(_x_p9_l0 != 0)) && ( !(_x_p9_l1 != 0))) && ((p9_l0 != 0) && ( !(p9_l1 != 0)))))))) && ((((id == _x_id) && (p9_x == _x_p9_x)) && (( !(p9_x <= 2.0)) && (id == 10))) || ( !(((delta == 0.0) && (turn == 10)) && (((p9_l0 != 0) && ( !(p9_l1 != 0))) && ((_x_p9_l0 != 0) && (_x_p9_l1 != 0))))))) && (((( !(_x_p9_l0 != 0)) && ( !(_x_p9_l1 != 0))) && ((_x_id == 0) && (p9_x == _x_p9_x))) || ( !(((p9_l0 != 0) && (p9_l1 != 0)) && ((delta == 0.0) && (turn == 10)))))) && ((((((((((((( !(_x_p8_l0 != 0)) && ( !(_x_p8_l1 != 0))) || ((_x_p8_l0 != 0) && ( !(_x_p8_l1 != 0)))) || (((_x_p8_l1 != 0) && ( !(_x_p8_l0 != 0))) || ((_x_p8_l0 != 0) && (_x_p8_l1 != 0)))) && ((_x_p8_x <= 2.0) || ( !((_x_p8_l1 != 0) && ( !(_x_p8_l0 != 0)))))) && (((((p8_l0 != 0) == (_x_p8_l0 != 0)) && ((p8_l1 != 0) == (_x_p8_l1 != 0))) && ((delta + (p8_x + (-1.0 * _x_p8_x))) == 0.0)) || ( !(( !(delta <= 0.0)) || ( !(turn == 9)))))) && ((((id == 0) && ((_x_p8_l1 != 0) && ( !(_x_p8_l0 != 0)))) && ((id == _x_id) && (_x_p8_x == 0.0))) || ( !((( !(p8_l0 != 0)) && ( !(p8_l1 != 0))) && ((delta == 0.0) && (turn == 9)))))) && (((((_x_p8_l0 != 0) && ( !(_x_p8_l1 != 0))) && (p8_x <= 2.0)) && ((_x_p8_x == 0.0) && (_x_id == 9))) || ( !(((p8_l1 != 0) && ( !(p8_l0 != 0))) && ((delta == 0.0) && (turn == 9)))))) && (((( !(_x_p8_l0 != 0)) && ( !(_x_p8_l1 != 0))) || ((_x_p8_l0 != 0) && (_x_p8_l1 != 0))) || ( !(((p8_l0 != 0) && ( !(p8_l1 != 0))) && ((delta == 0.0) && (turn == 9)))))) && ((((id == _x_id) && (_x_p8_x == 0.0)) && (( !(p8_x <= 2.0)) && ( !(id == 9)))) || ( !(((delta == 0.0) && (turn == 9)) && ((( !(_x_p8_l0 != 0)) && ( !(_x_p8_l1 != 0))) && ((p8_l0 != 0) && ( !(p8_l1 != 0)))))))) && ((((id == _x_id) && (p8_x == _x_p8_x)) && (( !(p8_x <= 2.0)) && (id == 9))) || ( !(((delta == 0.0) && (turn == 9)) && (((p8_l0 != 0) && ( !(p8_l1 != 0))) && ((_x_p8_l0 != 0) && (_x_p8_l1 != 0))))))) && (((( !(_x_p8_l0 != 0)) && ( !(_x_p8_l1 != 0))) && ((_x_id == 0) && (p8_x == _x_p8_x))) || ( !(((p8_l0 != 0) && (p8_l1 != 0)) && ((delta == 0.0) && (turn == 9)))))) && ((((((((((((( !(_x_p7_l0 != 0)) && ( !(_x_p7_l1 != 0))) || ((_x_p7_l0 != 0) && ( !(_x_p7_l1 != 0)))) || (((_x_p7_l1 != 0) && ( !(_x_p7_l0 != 0))) || ((_x_p7_l0 != 0) && (_x_p7_l1 != 0)))) && ((_x_p7_x <= 2.0) || ( !((_x_p7_l1 != 0) && ( !(_x_p7_l0 != 0)))))) && (((((p7_l0 != 0) == (_x_p7_l0 != 0)) && ((p7_l1 != 0) == (_x_p7_l1 != 0))) && ((delta + (p7_x + (-1.0 * _x_p7_x))) == 0.0)) || ( !(( !(delta <= 0.0)) || ( !(turn == 8)))))) && ((((id == 0) && ((_x_p7_l1 != 0) && ( !(_x_p7_l0 != 0)))) && ((id == _x_id) && (_x_p7_x == 0.0))) || ( !((( !(p7_l0 != 0)) && ( !(p7_l1 != 0))) && ((delta == 0.0) && (turn == 8)))))) && (((((_x_p7_l0 != 0) && ( !(_x_p7_l1 != 0))) && (p7_x <= 2.0)) && ((_x_p7_x == 0.0) && (_x_id == 8))) || ( !(((p7_l1 != 0) && ( !(p7_l0 != 0))) && ((delta == 0.0) && (turn == 8)))))) && (((( !(_x_p7_l0 != 0)) && ( !(_x_p7_l1 != 0))) || ((_x_p7_l0 != 0) && (_x_p7_l1 != 0))) || ( !(((p7_l0 != 0) && ( !(p7_l1 != 0))) && ((delta == 0.0) && (turn == 8)))))) && ((((id == _x_id) && (_x_p7_x == 0.0)) && (( !(p7_x <= 2.0)) && ( !(id == 8)))) || ( !(((delta == 0.0) && (turn == 8)) && ((( !(_x_p7_l0 != 0)) && ( !(_x_p7_l1 != 0))) && ((p7_l0 != 0) && ( !(p7_l1 != 0)))))))) && ((((id == _x_id) && (p7_x == _x_p7_x)) && (( !(p7_x <= 2.0)) && (id == 8))) || ( !(((delta == 0.0) && (turn == 8)) && (((p7_l0 != 0) && ( !(p7_l1 != 0))) && ((_x_p7_l0 != 0) && (_x_p7_l1 != 0))))))) && (((( !(_x_p7_l0 != 0)) && ( !(_x_p7_l1 != 0))) && ((_x_id == 0) && (p7_x == _x_p7_x))) || ( !(((p7_l0 != 0) && (p7_l1 != 0)) && ((delta == 0.0) && (turn == 8)))))) && ((((((((((((( !(_x_p6_l0 != 0)) && ( !(_x_p6_l1 != 0))) || ((_x_p6_l0 != 0) && ( !(_x_p6_l1 != 0)))) || (((_x_p6_l1 != 0) && ( !(_x_p6_l0 != 0))) || ((_x_p6_l0 != 0) && (_x_p6_l1 != 0)))) && ((_x_p6_x <= 2.0) || ( !((_x_p6_l1 != 0) && ( !(_x_p6_l0 != 0)))))) && (((((p6_l0 != 0) == (_x_p6_l0 != 0)) && ((p6_l1 != 0) == (_x_p6_l1 != 0))) && ((delta + (p6_x + (-1.0 * _x_p6_x))) == 0.0)) || ( !(( !(delta <= 0.0)) || ( !(turn == 7)))))) && ((((id == 0) && ((_x_p6_l1 != 0) && ( !(_x_p6_l0 != 0)))) && ((id == _x_id) && (_x_p6_x == 0.0))) || ( !((( !(p6_l0 != 0)) && ( !(p6_l1 != 0))) && ((delta == 0.0) && (turn == 7)))))) && (((((_x_p6_l0 != 0) && ( !(_x_p6_l1 != 0))) && (p6_x <= 2.0)) && ((_x_p6_x == 0.0) && (_x_id == 7))) || ( !(((p6_l1 != 0) && ( !(p6_l0 != 0))) && ((delta == 0.0) && (turn == 7)))))) && (((( !(_x_p6_l0 != 0)) && ( !(_x_p6_l1 != 0))) || ((_x_p6_l0 != 0) && (_x_p6_l1 != 0))) || ( !(((p6_l0 != 0) && ( !(p6_l1 != 0))) && ((delta == 0.0) && (turn == 7)))))) && ((((id == _x_id) && (_x_p6_x == 0.0)) && (( !(p6_x <= 2.0)) && ( !(id == 7)))) || ( !(((delta == 0.0) && (turn == 7)) && ((( !(_x_p6_l0 != 0)) && ( !(_x_p6_l1 != 0))) && ((p6_l0 != 0) && ( !(p6_l1 != 0)))))))) && ((((id == _x_id) && (p6_x == _x_p6_x)) && (( !(p6_x <= 2.0)) && (id == 7))) || ( !(((delta == 0.0) && (turn == 7)) && (((p6_l0 != 0) && ( !(p6_l1 != 0))) && ((_x_p6_l0 != 0) && (_x_p6_l1 != 0))))))) && (((( !(_x_p6_l0 != 0)) && ( !(_x_p6_l1 != 0))) && ((_x_id == 0) && (p6_x == _x_p6_x))) || ( !(((p6_l0 != 0) && (p6_l1 != 0)) && ((delta == 0.0) && (turn == 7)))))) && ((((((((((((( !(_x_p5_l0 != 0)) && ( !(_x_p5_l1 != 0))) || ((_x_p5_l0 != 0) && ( !(_x_p5_l1 != 0)))) || (((_x_p5_l1 != 0) && ( !(_x_p5_l0 != 0))) || ((_x_p5_l0 != 0) && (_x_p5_l1 != 0)))) && ((_x_p5_x <= 2.0) || ( !((_x_p5_l1 != 0) && ( !(_x_p5_l0 != 0)))))) && (((((p5_l0 != 0) == (_x_p5_l0 != 0)) && ((p5_l1 != 0) == (_x_p5_l1 != 0))) && ((delta + (p5_x + (-1.0 * _x_p5_x))) == 0.0)) || ( !(( !(delta <= 0.0)) || ( !(turn == 6)))))) && ((((id == 0) && ((_x_p5_l1 != 0) && ( !(_x_p5_l0 != 0)))) && ((id == _x_id) && (_x_p5_x == 0.0))) || ( !((( !(p5_l0 != 0)) && ( !(p5_l1 != 0))) && ((delta == 0.0) && (turn == 6)))))) && (((((_x_p5_l0 != 0) && ( !(_x_p5_l1 != 0))) && (p5_x <= 2.0)) && ((_x_p5_x == 0.0) && (_x_id == 6))) || ( !(((p5_l1 != 0) && ( !(p5_l0 != 0))) && ((delta == 0.0) && (turn == 6)))))) && (((( !(_x_p5_l0 != 0)) && ( !(_x_p5_l1 != 0))) || ((_x_p5_l0 != 0) && (_x_p5_l1 != 0))) || ( !(((p5_l0 != 0) && ( !(p5_l1 != 0))) && ((delta == 0.0) && (turn == 6)))))) && ((((id == _x_id) && (_x_p5_x == 0.0)) && (( !(p5_x <= 2.0)) && ( !(id == 6)))) || ( !(((delta == 0.0) && (turn == 6)) && ((( !(_x_p5_l0 != 0)) && ( !(_x_p5_l1 != 0))) && ((p5_l0 != 0) && ( !(p5_l1 != 0)))))))) && ((((id == _x_id) && (p5_x == _x_p5_x)) && (( !(p5_x <= 2.0)) && (id == 6))) || ( !(((delta == 0.0) && (turn == 6)) && (((p5_l0 != 0) && ( !(p5_l1 != 0))) && ((_x_p5_l0 != 0) && (_x_p5_l1 != 0))))))) && (((( !(_x_p5_l0 != 0)) && ( !(_x_p5_l1 != 0))) && ((_x_id == 0) && (p5_x == _x_p5_x))) || ( !(((p5_l0 != 0) && (p5_l1 != 0)) && ((delta == 0.0) && (turn == 6)))))) && ((((((((((((( !(_x_p4_l0 != 0)) && ( !(_x_p4_l1 != 0))) || ((_x_p4_l0 != 0) && ( !(_x_p4_l1 != 0)))) || (((_x_p4_l1 != 0) && ( !(_x_p4_l0 != 0))) || ((_x_p4_l0 != 0) && (_x_p4_l1 != 0)))) && ((_x_p4_x <= 2.0) || ( !((_x_p4_l1 != 0) && ( !(_x_p4_l0 != 0)))))) && (((((p4_l0 != 0) == (_x_p4_l0 != 0)) && ((p4_l1 != 0) == (_x_p4_l1 != 0))) && ((delta + (p4_x + (-1.0 * _x_p4_x))) == 0.0)) || ( !(( !(delta <= 0.0)) || ( !(turn == 5)))))) && ((((id == 0) && ((_x_p4_l1 != 0) && ( !(_x_p4_l0 != 0)))) && ((id == _x_id) && (_x_p4_x == 0.0))) || ( !((( !(p4_l0 != 0)) && ( !(p4_l1 != 0))) && ((delta == 0.0) && (turn == 5)))))) && (((((_x_p4_l0 != 0) && ( !(_x_p4_l1 != 0))) && (p4_x <= 2.0)) && ((_x_p4_x == 0.0) && (_x_id == 5))) || ( !(((p4_l1 != 0) && ( !(p4_l0 != 0))) && ((delta == 0.0) && (turn == 5)))))) && (((( !(_x_p4_l0 != 0)) && ( !(_x_p4_l1 != 0))) || ((_x_p4_l0 != 0) && (_x_p4_l1 != 0))) || ( !(((p4_l0 != 0) && ( !(p4_l1 != 0))) && ((delta == 0.0) && (turn == 5)))))) && ((((id == _x_id) && (_x_p4_x == 0.0)) && (( !(p4_x <= 2.0)) && ( !(id == 5)))) || ( !(((delta == 0.0) && (turn == 5)) && ((( !(_x_p4_l0 != 0)) && ( !(_x_p4_l1 != 0))) && ((p4_l0 != 0) && ( !(p4_l1 != 0)))))))) && ((((id == _x_id) && (p4_x == _x_p4_x)) && (( !(p4_x <= 2.0)) && (id == 5))) || ( !(((delta == 0.0) && (turn == 5)) && (((p4_l0 != 0) && ( !(p4_l1 != 0))) && ((_x_p4_l0 != 0) && (_x_p4_l1 != 0))))))) && (((( !(_x_p4_l0 != 0)) && ( !(_x_p4_l1 != 0))) && ((_x_id == 0) && (p4_x == _x_p4_x))) || ( !(((p4_l0 != 0) && (p4_l1 != 0)) && ((delta == 0.0) && (turn == 5)))))) && ((((((((((((( !(_x_p3_l0 != 0)) && ( !(_x_p3_l1 != 0))) || ((_x_p3_l0 != 0) && ( !(_x_p3_l1 != 0)))) || (((_x_p3_l1 != 0) && ( !(_x_p3_l0 != 0))) || ((_x_p3_l0 != 0) && (_x_p3_l1 != 0)))) && ((_x_p3_x <= 2.0) || ( !((_x_p3_l1 != 0) && ( !(_x_p3_l0 != 0)))))) && (((((p3_l0 != 0) == (_x_p3_l0 != 0)) && ((p3_l1 != 0) == (_x_p3_l1 != 0))) && ((delta + (p3_x + (-1.0 * _x_p3_x))) == 0.0)) || ( !(( !(delta <= 0.0)) || ( !(turn == 4)))))) && ((((id == 0) && ((_x_p3_l1 != 0) && ( !(_x_p3_l0 != 0)))) && ((id == _x_id) && (_x_p3_x == 0.0))) || ( !((( !(p3_l0 != 0)) && ( !(p3_l1 != 0))) && ((delta == 0.0) && (turn == 4)))))) && (((((_x_p3_l0 != 0) && ( !(_x_p3_l1 != 0))) && (p3_x <= 2.0)) && ((_x_p3_x == 0.0) && (_x_id == 4))) || ( !(((p3_l1 != 0) && ( !(p3_l0 != 0))) && ((delta == 0.0) && (turn == 4)))))) && (((( !(_x_p3_l0 != 0)) && ( !(_x_p3_l1 != 0))) || ((_x_p3_l0 != 0) && (_x_p3_l1 != 0))) || ( !(((p3_l0 != 0) && ( !(p3_l1 != 0))) && ((delta == 0.0) && (turn == 4)))))) && ((((id == _x_id) && (_x_p3_x == 0.0)) && (( !(p3_x <= 2.0)) && ( !(id == 4)))) || ( !(((delta == 0.0) && (turn == 4)) && ((( !(_x_p3_l0 != 0)) && ( !(_x_p3_l1 != 0))) && ((p3_l0 != 0) && ( !(p3_l1 != 0)))))))) && ((((id == _x_id) && (p3_x == _x_p3_x)) && (( !(p3_x <= 2.0)) && (id == 4))) || ( !(((delta == 0.0) && (turn == 4)) && (((p3_l0 != 0) && ( !(p3_l1 != 0))) && ((_x_p3_l0 != 0) && (_x_p3_l1 != 0))))))) && (((( !(_x_p3_l0 != 0)) && ( !(_x_p3_l1 != 0))) && ((_x_id == 0) && (p3_x == _x_p3_x))) || ( !(((p3_l0 != 0) && (p3_l1 != 0)) && ((delta == 0.0) && (turn == 4)))))) && ((((((((((((( !(_x_p2_l0 != 0)) && ( !(_x_p2_l1 != 0))) || ((_x_p2_l0 != 0) && ( !(_x_p2_l1 != 0)))) || (((_x_p2_l1 != 0) && ( !(_x_p2_l0 != 0))) || ((_x_p2_l0 != 0) && (_x_p2_l1 != 0)))) && ((_x_p2_x <= 2.0) || ( !((_x_p2_l1 != 0) && ( !(_x_p2_l0 != 0)))))) && (((((p2_l0 != 0) == (_x_p2_l0 != 0)) && ((p2_l1 != 0) == (_x_p2_l1 != 0))) && ((delta + (p2_x + (-1.0 * _x_p2_x))) == 0.0)) || ( !(( !(delta <= 0.0)) || ( !(turn == 3)))))) && ((((id == 0) && ((_x_p2_l1 != 0) && ( !(_x_p2_l0 != 0)))) && ((id == _x_id) && (_x_p2_x == 0.0))) || ( !((( !(p2_l0 != 0)) && ( !(p2_l1 != 0))) && ((delta == 0.0) && (turn == 3)))))) && (((((_x_p2_l0 != 0) && ( !(_x_p2_l1 != 0))) && (p2_x <= 2.0)) && ((_x_p2_x == 0.0) && (_x_id == 3))) || ( !(((p2_l1 != 0) && ( !(p2_l0 != 0))) && ((delta == 0.0) && (turn == 3)))))) && (((( !(_x_p2_l0 != 0)) && ( !(_x_p2_l1 != 0))) || ((_x_p2_l0 != 0) && (_x_p2_l1 != 0))) || ( !(((p2_l0 != 0) && ( !(p2_l1 != 0))) && ((delta == 0.0) && (turn == 3)))))) && ((((id == _x_id) && (_x_p2_x == 0.0)) && (( !(p2_x <= 2.0)) && ( !(id == 3)))) || ( !(((delta == 0.0) && (turn == 3)) && ((( !(_x_p2_l0 != 0)) && ( !(_x_p2_l1 != 0))) && ((p2_l0 != 0) && ( !(p2_l1 != 0)))))))) && ((((id == _x_id) && (p2_x == _x_p2_x)) && (( !(p2_x <= 2.0)) && (id == 3))) || ( !(((delta == 0.0) && (turn == 3)) && (((p2_l0 != 0) && ( !(p2_l1 != 0))) && ((_x_p2_l0 != 0) && (_x_p2_l1 != 0))))))) && (((( !(_x_p2_l0 != 0)) && ( !(_x_p2_l1 != 0))) && ((_x_id == 0) && (p2_x == _x_p2_x))) || ( !(((p2_l0 != 0) && (p2_l1 != 0)) && ((delta == 0.0) && (turn == 3)))))) && ((((((((((((( !(_x_p1_l0 != 0)) && ( !(_x_p1_l1 != 0))) || ((_x_p1_l0 != 0) && ( !(_x_p1_l1 != 0)))) || (((_x_p1_l1 != 0) && ( !(_x_p1_l0 != 0))) || ((_x_p1_l0 != 0) && (_x_p1_l1 != 0)))) && ((_x_p1_x <= 2.0) || ( !((_x_p1_l1 != 0) && ( !(_x_p1_l0 != 0)))))) && (((((p1_l0 != 0) == (_x_p1_l0 != 0)) && ((p1_l1 != 0) == (_x_p1_l1 != 0))) && ((delta + (p1_x + (-1.0 * _x_p1_x))) == 0.0)) || ( !(( !(delta <= 0.0)) || ( !(turn == 2)))))) && ((((id == 0) && ((_x_p1_l1 != 0) && ( !(_x_p1_l0 != 0)))) && ((id == _x_id) && (_x_p1_x == 0.0))) || ( !((( !(p1_l0 != 0)) && ( !(p1_l1 != 0))) && ((delta == 0.0) && (turn == 2)))))) && (((((_x_p1_l0 != 0) && ( !(_x_p1_l1 != 0))) && (p1_x <= 2.0)) && ((_x_p1_x == 0.0) && (_x_id == 2))) || ( !(((p1_l1 != 0) && ( !(p1_l0 != 0))) && ((delta == 0.0) && (turn == 2)))))) && (((( !(_x_p1_l0 != 0)) && ( !(_x_p1_l1 != 0))) || ((_x_p1_l0 != 0) && (_x_p1_l1 != 0))) || ( !(((p1_l0 != 0) && ( !(p1_l1 != 0))) && ((delta == 0.0) && (turn == 2)))))) && ((((id == _x_id) && (_x_p1_x == 0.0)) && (( !(p1_x <= 2.0)) && ( !(id == 2)))) || ( !(((delta == 0.0) && (turn == 2)) && ((( !(_x_p1_l0 != 0)) && ( !(_x_p1_l1 != 0))) && ((p1_l0 != 0) && ( !(p1_l1 != 0)))))))) && ((((id == _x_id) && (p1_x == _x_p1_x)) && (( !(p1_x <= 2.0)) && (id == 2))) || ( !(((delta == 0.0) && (turn == 2)) && (((p1_l0 != 0) && ( !(p1_l1 != 0))) && ((_x_p1_l0 != 0) && (_x_p1_l1 != 0))))))) && (((( !(_x_p1_l0 != 0)) && ( !(_x_p1_l1 != 0))) && ((_x_id == 0) && (p1_x == _x_p1_x))) || ( !(((p1_l0 != 0) && (p1_l1 != 0)) && ((delta == 0.0) && (turn == 2)))))) && ((((((((((((( !(_x_p0_l0 != 0)) && ( !(_x_p0_l1 != 0))) || ((_x_p0_l0 != 0) && ( !(_x_p0_l1 != 0)))) || (((_x_p0_l1 != 0) && ( !(_x_p0_l0 != 0))) || ((_x_p0_l0 != 0) && (_x_p0_l1 != 0)))) && ((_x_p0_x <= 2.0) || ( !((_x_p0_l1 != 0) && ( !(_x_p0_l0 != 0)))))) && (((((p0_l0 != 0) == (_x_p0_l0 != 0)) && ((p0_l1 != 0) == (_x_p0_l1 != 0))) && ((delta + (p0_x + (-1.0 * _x_p0_x))) == 0.0)) || ( !(( !(delta <= 0.0)) || ( !(turn == 1)))))) && (((((_x_p0_l1 != 0) && ( !(_x_p0_l0 != 0))) && (id == 0)) && ((_x_p0_x == 0.0) && (id == _x_id))) || ( !((( !(p0_l0 != 0)) && ( !(p0_l1 != 0))) && ((turn == 1) && (delta == 0.0)))))) && (((((_x_p0_l0 != 0) && ( !(_x_p0_l1 != 0))) && (p0_x <= 2.0)) && ((_x_p0_x == 0.0) && (_x_id == 1))) || ( !(((p0_l1 != 0) && ( !(p0_l0 != 0))) && ((turn == 1) && (delta == 0.0)))))) && (((( !(_x_p0_l0 != 0)) && ( !(_x_p0_l1 != 0))) || ((_x_p0_l0 != 0) && (_x_p0_l1 != 0))) || ( !(((p0_l0 != 0) && ( !(p0_l1 != 0))) && ((turn == 1) && (delta == 0.0)))))) && ((((_x_p0_x == 0.0) && (id == _x_id)) && (( !(p0_x <= 2.0)) && ( !(id == 1)))) || ( !(((turn == 1) && (delta == 0.0)) && ((( !(_x_p0_l0 != 0)) && ( !(_x_p0_l1 != 0))) && ((p0_l0 != 0) && ( !(p0_l1 != 0)))))))) && ((((id == _x_id) && (p0_x == _x_p0_x)) && (( !(p0_x <= 2.0)) && (id == 1))) || ( !(((turn == 1) && (delta == 0.0)) && (((p0_l0 != 0) && ( !(p0_l1 != 0))) && ((_x_p0_l0 != 0) && (_x_p0_l1 != 0))))))) && (((( !(_x_p0_l0 != 0)) && ( !(_x_p0_l1 != 0))) && ((p0_x == _x_p0_x) && (_x_id == 0))) || ( !(((p0_l0 != 0) && (p0_l1 != 0)) && ((turn == 1) && (delta == 0.0)))))) && (((((id == 14) || ((id == 13) || ((id == 12) || ((id == 11) || ((id == 10) || ((id == 9) || ((id == 8) || ((id == 7) || ((id == 6) || ((id == 5) || ((id == 4) || ((id == 3) || ((id == 2) || ((id == 0) || (id == 1))))))))))))))) && ((((((((((((((_x_turn == 1) || (_x_turn == 2)) || (_x_turn == 3)) || (_x_turn == 4)) || (_x_turn == 5)) || (_x_turn == 6)) || (_x_turn == 7)) || (_x_turn == 8)) || (_x_turn == 9)) || (_x_turn == 10)) || (_x_turn == 11)) || (_x_turn == 12)) || (_x_turn == 13)) || (_x_turn == 14))) && (0.0 <= _x_delta)) && ((delta <= 0.0) || ((id == _x_id) && (turn == _x_turn)))))))))))))))))) && (((delta == _x__diverge_delta) || ( !(1.0 <= _diverge_delta))) && ((1.0 <= _diverge_delta) || ((delta + (_diverge_delta + (-1.0 * _x__diverge_delta))) == 0.0))));
    _diverge_delta = _x__diverge_delta;
    p12_l0 = _x_p12_l0;
    p12_x = _x_p12_x;
    p11_l0 = _x_p11_l0;
    p11_x = _x_p11_x;
    p10_l0 = _x_p10_l0;
    p10_x = _x_p10_x;
    p9_x = _x_p9_x;
    p2_l1 = _x_p2_l1;
    p6_x = _x_p6_x;
    p8_l1 = _x_p8_l1;
    p2_l0 = _x_p2_l0;
    p13_l0 = _x_p13_l0;
    p2_x = _x_p2_x;
    p1_l1 = _x_p1_l1;
    delta = _x_delta;
    p13_x = _x_p13_x;
    p0_l0 = _x_p0_l0;
    p7_l1 = _x_p7_l1;
    p0_x = _x_p0_x;
    p12_l1 = _x_p12_l1;
    p6_l0 = _x_p6_l0;
    turn = _x_turn;
    id = _x_id;
    p3_x = _x_p3_x;
    p9_l0 = _x_p9_l0;
    p1_x = _x_p1_x;
    p5_l1 = _x_p5_l1;
    p9_l1 = _x_p9_l1;
    p3_l0 = _x_p3_l0;
    p3_l1 = _x_p3_l1;
    p0_l1 = _x_p0_l1;
    p7_x = _x_p7_x;
    p4_x = _x_p4_x;
    p10_l1 = _x_p10_l1;
    p4_l0 = _x_p4_l0;
    p1_l0 = _x_p1_l0;
    p4_l1 = _x_p4_l1;
    p8_x = _x_p8_x;
    p5_x = _x_p5_x;
    p11_l1 = _x_p11_l1;
    p5_l0 = _x_p5_l0;
    p6_l1 = _x_p6_l1;
    p13_l1 = _x_p13_l1;
    p7_l0 = _x_p7_l0;
    p8_l0 = _x_p8_l0;

  }
}
