//@ ltl invariant negative: ( ( ([] (<> ( AP((p0_l0 != 0)) && AP((p0_l1 != 0))))) || (! ([] (<> ( AP((p0_l0 != 0)) && (! AP((p0_l1 != 0)))))))) || (! ([] (<> AP((1.0 <= _diverge_delta))))));

extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);

char __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}


float _diverge_delta, _x__diverge_delta;
char p1_l1, _x_p1_l1;
char p0_l1, _x_p0_l1;
char p0_l0, _x_p0_l0;
char p1_l0, _x_p1_l0;
float p0_x, _x_p0_x;
int turn, _x_turn;
int id, _x_id;
float p1_x, _x_p1_x;
float delta, _x_delta;

int main()
{
  _diverge_delta = __VERIFIER_nondet_float();
  p1_l1 = __VERIFIER_nondet_bool();
  p0_l1 = __VERIFIER_nondet_bool();
  p0_l0 = __VERIFIER_nondet_bool();
  p1_l0 = __VERIFIER_nondet_bool();
  p0_x = __VERIFIER_nondet_float();
  turn = __VERIFIER_nondet_int();
  id = __VERIFIER_nondet_int();
  p1_x = __VERIFIER_nondet_float();
  delta = __VERIFIER_nondet_float();

  int __ok = (((id == 0) && (((((( !(p1_l0 != 0)) && ( !(p1_l1 != 0))) && (p1_x == 0.0)) && (((( !(p1_l0 != 0)) && ( !(p1_l1 != 0))) || ((p1_l0 != 0) && ( !(p1_l1 != 0)))) || (((p1_l1 != 0) && ( !(p1_l0 != 0))) || ((p1_l0 != 0) && (p1_l1 != 0))))) && ((p1_x <= 2.0) || ( !((p1_l1 != 0) && ( !(p1_l0 != 0)))))) && (((((( !(p0_l0 != 0)) && ( !(p0_l1 != 0))) && (p0_x == 0.0)) && (((( !(p0_l0 != 0)) && ( !(p0_l1 != 0))) || ((p0_l0 != 0) && ( !(p0_l1 != 0)))) || (((p0_l1 != 0) && ( !(p0_l0 != 0))) || ((p0_l0 != 0) && (p0_l1 != 0))))) && ((p0_x <= 2.0) || ( !((p0_l1 != 0) && ( !(p0_l0 != 0)))))) && (((0.0 <= delta) && ((id == 2) || ((id == 0) || (id == 1)))) && ((turn == 1) || (turn == 2)))))) && (delta == _diverge_delta));
  while (__ok) {
    _x__diverge_delta = __VERIFIER_nondet_float();
    _x_p1_l1 = __VERIFIER_nondet_bool();
    _x_p0_l1 = __VERIFIER_nondet_bool();
    _x_p0_l0 = __VERIFIER_nondet_bool();
    _x_p1_l0 = __VERIFIER_nondet_bool();
    _x_p0_x = __VERIFIER_nondet_float();
    _x_turn = __VERIFIER_nondet_int();
    _x_id = __VERIFIER_nondet_int();
    _x_p1_x = __VERIFIER_nondet_float();
    _x_delta = __VERIFIER_nondet_float();

    __ok = (((((((((((((( !(_x_p1_l0 != 0)) && ( !(_x_p1_l1 != 0))) || ((_x_p1_l0 != 0) && ( !(_x_p1_l1 != 0)))) || (((_x_p1_l1 != 0) && ( !(_x_p1_l0 != 0))) || ((_x_p1_l0 != 0) && (_x_p1_l1 != 0)))) && ((_x_p1_x <= 2.0) || ( !((_x_p1_l1 != 0) && ( !(_x_p1_l0 != 0)))))) && (((((p1_l0 != 0) == (_x_p1_l0 != 0)) && ((p1_l1 != 0) == (_x_p1_l1 != 0))) && ((delta + (p1_x + (-1.0 * _x_p1_x))) == 0.0)) || ( !(( !(delta <= 0.0)) || ( !(turn == 2)))))) && ((((id == 0) && ((_x_p1_l1 != 0) && ( !(_x_p1_l0 != 0)))) && ((id == _x_id) && (_x_p1_x == 0.0))) || ( !((( !(p1_l0 != 0)) && ( !(p1_l1 != 0))) && ((delta == 0.0) && (turn == 2)))))) && (((((_x_p1_l0 != 0) && ( !(_x_p1_l1 != 0))) && (p1_x <= 2.0)) && ((_x_p1_x == 0.0) && (_x_id == 2))) || ( !(((p1_l1 != 0) && ( !(p1_l0 != 0))) && ((delta == 0.0) && (turn == 2)))))) && (((( !(_x_p1_l0 != 0)) && ( !(_x_p1_l1 != 0))) || ((_x_p1_l0 != 0) && (_x_p1_l1 != 0))) || ( !(((p1_l0 != 0) && ( !(p1_l1 != 0))) && ((delta == 0.0) && (turn == 2)))))) && ((((id == _x_id) && (_x_p1_x == 0.0)) && (( !(p1_x <= 2.0)) && ( !(id == 2)))) || ( !(((delta == 0.0) && (turn == 2)) && ((( !(_x_p1_l0 != 0)) && ( !(_x_p1_l1 != 0))) && ((p1_l0 != 0) && ( !(p1_l1 != 0)))))))) && ((((id == _x_id) && (p1_x == _x_p1_x)) && (( !(p1_x <= 2.0)) && (id == 2))) || ( !(((delta == 0.0) && (turn == 2)) && (((p1_l0 != 0) && ( !(p1_l1 != 0))) && ((_x_p1_l0 != 0) && (_x_p1_l1 != 0))))))) && (((( !(_x_p1_l0 != 0)) && ( !(_x_p1_l1 != 0))) && ((_x_id == 0) && (p1_x == _x_p1_x))) || ( !(((p1_l0 != 0) && (p1_l1 != 0)) && ((delta == 0.0) && (turn == 2)))))) && ((((((((((((( !(_x_p0_l0 != 0)) && ( !(_x_p0_l1 != 0))) || ((_x_p0_l0 != 0) && ( !(_x_p0_l1 != 0)))) || (((_x_p0_l1 != 0) && ( !(_x_p0_l0 != 0))) || ((_x_p0_l0 != 0) && (_x_p0_l1 != 0)))) && ((_x_p0_x <= 2.0) || ( !((_x_p0_l1 != 0) && ( !(_x_p0_l0 != 0)))))) && (((((p0_l0 != 0) == (_x_p0_l0 != 0)) && ((p0_l1 != 0) == (_x_p0_l1 != 0))) && ((delta + (p0_x + (-1.0 * _x_p0_x))) == 0.0)) || ( !(( !(delta <= 0.0)) || ( !(turn == 1)))))) && (((((_x_p0_l1 != 0) && ( !(_x_p0_l0 != 0))) && (id == 0)) && ((_x_p0_x == 0.0) && (id == _x_id))) || ( !((( !(p0_l0 != 0)) && ( !(p0_l1 != 0))) && ((turn == 1) && (delta == 0.0)))))) && (((((_x_p0_l0 != 0) && ( !(_x_p0_l1 != 0))) && (p0_x <= 2.0)) && ((_x_p0_x == 0.0) && (_x_id == 1))) || ( !(((p0_l1 != 0) && ( !(p0_l0 != 0))) && ((turn == 1) && (delta == 0.0)))))) && (((( !(_x_p0_l0 != 0)) && ( !(_x_p0_l1 != 0))) || ((_x_p0_l0 != 0) && (_x_p0_l1 != 0))) || ( !(((p0_l0 != 0) && ( !(p0_l1 != 0))) && ((turn == 1) && (delta == 0.0)))))) && ((((_x_p0_x == 0.0) && (id == _x_id)) && (( !(p0_x <= 2.0)) && ( !(id == 1)))) || ( !(((turn == 1) && (delta == 0.0)) && ((( !(_x_p0_l0 != 0)) && ( !(_x_p0_l1 != 0))) && ((p0_l0 != 0) && ( !(p0_l1 != 0)))))))) && ((((id == _x_id) && (p0_x == _x_p0_x)) && (( !(p0_x <= 2.0)) && (id == 1))) || ( !(((turn == 1) && (delta == 0.0)) && (((p0_l0 != 0) && ( !(p0_l1 != 0))) && ((_x_p0_l0 != 0) && (_x_p0_l1 != 0))))))) && (((( !(_x_p0_l0 != 0)) && ( !(_x_p0_l1 != 0))) && ((p0_x == _x_p0_x) && (_x_id == 0))) || ( !(((p0_l0 != 0) && (p0_l1 != 0)) && ((turn == 1) && (delta == 0.0)))))) && (((((id == 2) || ((id == 0) || (id == 1))) && ((_x_turn == 1) || (_x_turn == 2))) && (0.0 <= _x_delta)) && ((delta <= 0.0) || ((id == _x_id) && (turn == _x_turn)))))) && (((delta == _x__diverge_delta) || ( !(1.0 <= _diverge_delta))) && ((1.0 <= _diverge_delta) || ((delta + (_diverge_delta + (-1.0 * _x__diverge_delta))) == 0.0))));
    _diverge_delta = _x__diverge_delta;
    p1_l1 = _x_p1_l1;
    p0_l1 = _x_p0_l1;
    p0_l0 = _x_p0_l0;
    p1_l0 = _x_p1_l0;
    p0_x = _x_p0_x;
    turn = _x_turn;
    id = _x_id;
    p1_x = _x_p1_x;
    delta = _x_delta;

  }
}
