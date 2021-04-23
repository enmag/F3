//@ ltl invariant negative: ( (<> ([] ( (! AP((delta <= 0.0))) && (! AP((leader_v <= 0.0)))))) || (! ([] (<> AP((1.0 <= _diverge_delta))))));

extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);

char __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}


float _diverge_delta, _x__diverge_delta;
float follower0_dist, _x_follower0_dist;
float follower0_v, _x_follower0_v;
float follower0_a, _x_follower0_a;
float leader_c, _x_leader_c;
float leader_v, _x_leader_v;
float leader_a, _x_leader_a;
float follower0_c, _x_follower0_c;
float delta, _x_delta;

int main()
{
  _diverge_delta = __VERIFIER_nondet_float();
  follower0_dist = __VERIFIER_nondet_float();
  follower0_v = __VERIFIER_nondet_float();
  follower0_a = __VERIFIER_nondet_float();
  leader_c = __VERIFIER_nondet_float();
  leader_v = __VERIFIER_nondet_float();
  leader_a = __VERIFIER_nondet_float();
  follower0_c = __VERIFIER_nondet_float();
  delta = __VERIFIER_nondet_float();

  int __ok = ((((0.0 <= delta) && (((leader_a == 0.0) && ((leader_v == 0.0) && (leader_c == 0.0))) && ((((0.0 <= leader_c) && (leader_c <= 1.0)) && ((0.0 <= leader_v) && (0.0 <= (leader_v + (delta * leader_a))))) && ((-1.0 <= leader_a) && (leader_a <= 2.0))))) && ((((follower0_a == 0.0) && (follower0_v == 0.0)) && ((follower0_c == 0.0) && (follower0_dist == 1.0))) && ((((0.0 <= follower0_c) && (follower0_c <= 1.0)) && ((0.0 <= follower0_v) && (0.0 <= (follower0_v + (delta * follower0_a))))) && ((-1.0 <= follower0_a) && (follower0_a <= 2.0))))) && (delta == _diverge_delta));
  while (__ok) {
    _x__diverge_delta = __VERIFIER_nondet_float();
    _x_follower0_dist = __VERIFIER_nondet_float();
    _x_follower0_v = __VERIFIER_nondet_float();
    _x_follower0_a = __VERIFIER_nondet_float();
    _x_leader_c = __VERIFIER_nondet_float();
    _x_leader_v = __VERIFIER_nondet_float();
    _x_leader_a = __VERIFIER_nondet_float();
    _x_follower0_c = __VERIFIER_nondet_float();
    _x_delta = __VERIFIER_nondet_float();

    __ok = ((((0.0 <= _x_delta) && (((((0.0 <= _x_leader_c) && (_x_leader_c <= 1.0)) && ((0.0 <= _x_leader_v) && (0.0 <= (_x_leader_v + (delta * _x_leader_a))))) && ((-1.0 <= _x_leader_a) && (_x_leader_a <= 2.0))) && ((((((_x_leader_c == 0.0) && (delta == 0.0)) || ( !(leader_c == 1.0))) && ((1.0 <= leader_c) || ((delta + (leader_c + (-1.0 * _x_leader_c))) == 0.0))) && (((delta == 0.0) && ((leader_c == 1.0) && (_x_leader_c == 0.0))) || ((leader_a == _x_leader_a) || (_x_leader_a == 0.0)))) && (((leader_v + ((-1.0 * _x_leader_v) + (delta * leader_a))) == 0.0) || ((_x_leader_a == 0.0) && (_x_leader_v == 0.0)))))) && (((((0.0 <= _x_follower0_c) && (_x_follower0_c <= 1.0)) && ((0.0 <= _x_follower0_v) && (0.0 <= (_x_follower0_v + (delta * _x_follower0_a))))) && ((-1.0 <= _x_follower0_a) && (_x_follower0_a <= 2.0))) && (((((((delta == 0.0) && (_x_follower0_c == 0.0)) || ( !(follower0_c == 1.0))) && ((1.0 <= follower0_c) || ((delta + (-1.0 * _x_follower0_c)) == -1.0))) && (( !((_x_follower0_a + ((-2.0 * follower0_v) + ((2.0 * follower0_dist) + (-1.0 * ((_x_follower0_a + follower0_v) * (_x_follower0_a + follower0_v)))))) <= 0.0)) || ( !((_x_follower0_c == 0.0) && ((delta == 0.0) && (follower0_c == 1.0)))))) && (((_x_follower0_c == 0.0) && ((delta == 0.0) && (follower0_c == 1.0))) || (follower0_a == _x_follower0_a))) && (((follower0_v + ((-1.0 * _x_follower0_v) + (delta * follower0_a))) == 0.0) && (follower0_dist == _x_follower0_dist))))) && (((delta == _x__diverge_delta) || ( !(1.0 <= _diverge_delta))) && ((1.0 <= _diverge_delta) || ((delta + (_diverge_delta + (-1.0 * _x__diverge_delta))) == 0.0))));
    _diverge_delta = _x__diverge_delta;
    follower0_dist = _x_follower0_dist;
    follower0_v = _x_follower0_v;
    follower0_a = _x_follower0_a;
    leader_c = _x_leader_c;
    leader_v = _x_leader_v;
    leader_a = _x_leader_a;
    follower0_c = _x_follower0_c;
    delta = _x_delta;

  }
}
