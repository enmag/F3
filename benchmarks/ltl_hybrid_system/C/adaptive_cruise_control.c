extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);
typedef enum {false, true} bool;
bool __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}

int main()
{
float _diverge_delta, _x__diverge_delta;
float delta, _x_delta;
bool _J282, _x__J282;
bool _J276, _x__J276;
float follower0_a, _x_follower0_a;
bool _J270, _x__J270;
float leader_a, _x_leader_a;
bool _J264, _x__J264;
float leader_travel, _x_leader_travel;
bool _EL_U_233, _x__EL_U_233;
float leader_v, _x_leader_v;
float follower0_v, _x_follower0_v;
bool _EL_U_235, _x__EL_U_235;
float leader_c, _x_leader_c;
bool _EL_U_237, _x__EL_U_237;
float follower0_c, _x_follower0_c;
bool _EL_U_239, _x__EL_U_239;
float follower0_dist, _x_follower0_dist;

  int __steps_to_fair = __VERIFIER_nondet_int();
  _diverge_delta = __VERIFIER_nondet_float();
  delta = __VERIFIER_nondet_float();
  _J282 = __VERIFIER_nondet_bool();
  _J276 = __VERIFIER_nondet_bool();
  follower0_a = __VERIFIER_nondet_float();
  _J270 = __VERIFIER_nondet_bool();
  leader_a = __VERIFIER_nondet_float();
  _J264 = __VERIFIER_nondet_bool();
  leader_travel = __VERIFIER_nondet_float();
  _EL_U_233 = __VERIFIER_nondet_bool();
  leader_v = __VERIFIER_nondet_float();
  follower0_v = __VERIFIER_nondet_float();
  _EL_U_235 = __VERIFIER_nondet_bool();
  leader_c = __VERIFIER_nondet_float();
  _EL_U_237 = __VERIFIER_nondet_bool();
  follower0_c = __VERIFIER_nondet_float();
  _EL_U_239 = __VERIFIER_nondet_bool();
  follower0_dist = __VERIFIER_nondet_float();

  bool __ok = (((((0.0 <= delta) && ((((leader_a == 0.0) && (leader_travel == 0.0)) && ((leader_v == 0.0) && (leader_c == 0.0))) && ((((0.0 <= leader_c) && (leader_c <= 1.0)) && ((0.0 <= leader_v) && (0.0 <= (leader_v + (delta * leader_a))))) && ((-1.0 <= leader_a) && (leader_a <= 2.0))))) && ((((follower0_a == 0.0) && (follower0_v == 0.0)) && ((follower0_c == 0.0) && (follower0_dist == 1.0))) && ((((0.0 <= follower0_c) && (follower0_c <= 1.0)) && ((0.0 <= follower0_v) && (0.0 <= (follower0_v + (delta * follower0_a))))) && ((-1.0 <= follower0_a) && (follower0_a <= 2.0))))) && (delta == _diverge_delta)) && ((((( !((_EL_U_239 || ( !((( !(delta <= 0.0)) && ( !(leader_v <= 0.0))) || _EL_U_237))) || (_EL_U_235 || ( !((1.0 <= _diverge_delta) || _EL_U_233))))) && ( !_J264)) && ( !_J270)) && ( !_J276)) && ( !_J282)));
  while (__steps_to_fair >= 0 && __ok) {
    if ((((_J264 && _J270) && _J276) && _J282)) {
      __steps_to_fair = __VERIFIER_nondet_int();
    } else {
      __steps_to_fair--;
    }
    _x__diverge_delta = __VERIFIER_nondet_float();
    _x_delta = __VERIFIER_nondet_float();
    _x__J282 = __VERIFIER_nondet_bool();
    _x__J276 = __VERIFIER_nondet_bool();
    _x_follower0_a = __VERIFIER_nondet_float();
    _x__J270 = __VERIFIER_nondet_bool();
    _x_leader_a = __VERIFIER_nondet_float();
    _x__J264 = __VERIFIER_nondet_bool();
    _x_leader_travel = __VERIFIER_nondet_float();
    _x__EL_U_233 = __VERIFIER_nondet_bool();
    _x_leader_v = __VERIFIER_nondet_float();
    _x_follower0_v = __VERIFIER_nondet_float();
    _x__EL_U_235 = __VERIFIER_nondet_bool();
    _x_leader_c = __VERIFIER_nondet_float();
    _x__EL_U_237 = __VERIFIER_nondet_bool();
    _x_follower0_c = __VERIFIER_nondet_float();
    _x__EL_U_239 = __VERIFIER_nondet_bool();
    _x_follower0_dist = __VERIFIER_nondet_float();

    __ok = (((((0.0 <= _x_delta) && (((((0.0 <= _x_leader_c) && (_x_leader_c <= 1.0)) && ((0.0 <= _x_leader_v) && (0.0 <= (_x_leader_v + (_x_delta * _x_leader_a))))) && ((-1.0 <= _x_leader_a) && (_x_leader_a <= 2.0))) && ((((((_x_leader_c == 0.0) && (delta == 0.0)) || ( !(leader_c == 1.0))) && ((1.0 <= leader_c) || ((delta + (leader_c + (-1.0 * _x_leader_c))) == 0.0))) && (((delta == 0.0) && ((leader_c == 1.0) && (_x_leader_c == 0.0))) || ((leader_a == _x_leader_a) || (_x_leader_a == 0.0)))) && ((((leader_v + ((-1.0 * _x_leader_v) + (delta * leader_a))) == 0.0) || ((_x_leader_a == 0.0) && (_x_leader_v == 0.0))) && ((leader_travel + ((-1.0 * _x_leader_travel) + ((delta * leader_v) + (((1.0/2.0) * leader_a) * (delta * delta))))) == 0.0))))) && (((((0.0 <= _x_follower0_c) && (_x_follower0_c <= 1.0)) && ((0.0 <= _x_follower0_v) && (0.0 <= (_x_follower0_v + (_x_delta * _x_follower0_a))))) && ((-1.0 <= _x_follower0_a) && (_x_follower0_a <= 2.0))) && (((((((delta == 0.0) && (_x_follower0_c == 0.0)) || ( !(follower0_c == 1.0))) && ((1.0 <= follower0_c) || ((delta + (follower0_c + (-1.0 * _x_follower0_c))) == 0.0))) && (( !((_x_follower0_a + ((-2.0 * follower0_v) + ((2.0 * follower0_dist) + (-1.0 * ((_x_follower0_a + follower0_v) * (_x_follower0_a + follower0_v)))))) <= 0.0)) || ( !((_x_follower0_c == 0.0) && ((delta == 0.0) && (follower0_c == 1.0)))))) && (((_x_follower0_c == 0.0) && ((delta == 0.0) && (follower0_c == 1.0))) || (follower0_a == _x_follower0_a))) && (((follower0_v + ((-1.0 * _x_follower0_v) + (delta * follower0_a))) == 0.0) && (follower0_dist == _x_follower0_dist))))) && (((delta == _x__diverge_delta) || ( !(1.0 <= _diverge_delta))) && ((1.0 <= _diverge_delta) || ((delta + (_diverge_delta + (-1.0 * _x__diverge_delta))) == 0.0)))) && ((((((_EL_U_235 == (_x__EL_U_235 || ( !(_x__EL_U_233 || (1.0 <= _x__diverge_delta))))) && ((_EL_U_233 == (_x__EL_U_233 || (1.0 <= _x__diverge_delta))) && ((_EL_U_237 == (_x__EL_U_237 || (( !(_x_leader_v <= 0.0)) && ( !(_x_delta <= 0.0))))) && (_EL_U_239 == (_x__EL_U_239 || ( !(_x__EL_U_237 || (( !(_x_leader_v <= 0.0)) && ( !(_x_delta <= 0.0)))))))))) && (_x__J264 == (( !(((_J264 && _J270) && _J276) && _J282)) && ((((_J264 && _J270) && _J276) && _J282) || (((( !(delta <= 0.0)) && ( !(leader_v <= 0.0))) || ( !((( !(delta <= 0.0)) && ( !(leader_v <= 0.0))) || _EL_U_237))) || _J264))))) && (_x__J270 == (( !(((_J264 && _J270) && _J276) && _J282)) && ((((_J264 && _J270) && _J276) && _J282) || ((( !((( !(delta <= 0.0)) && ( !(leader_v <= 0.0))) || _EL_U_237)) || ( !(_EL_U_239 || ( !((( !(delta <= 0.0)) && ( !(leader_v <= 0.0))) || _EL_U_237))))) || _J270))))) && (_x__J276 == (( !(((_J264 && _J270) && _J276) && _J282)) && ((((_J264 && _J270) && _J276) && _J282) || (((1.0 <= _diverge_delta) || ( !((1.0 <= _diverge_delta) || _EL_U_233))) || _J276))))) && (_x__J282 == (( !(((_J264 && _J270) && _J276) && _J282)) && ((((_J264 && _J270) && _J276) && _J282) || ((( !((1.0 <= _diverge_delta) || _EL_U_233)) || ( !(_EL_U_235 || ( !((1.0 <= _diverge_delta) || _EL_U_233))))) || _J282))))));
    _diverge_delta = _x__diverge_delta;
    delta = _x_delta;
    _J282 = _x__J282;
    _J276 = _x__J276;
    follower0_a = _x_follower0_a;
    _J270 = _x__J270;
    leader_a = _x_leader_a;
    _J264 = _x__J264;
    leader_travel = _x_leader_travel;
    _EL_U_233 = _x__EL_U_233;
    leader_v = _x_leader_v;
    follower0_v = _x_follower0_v;
    _EL_U_235 = _x__EL_U_235;
    leader_c = _x_leader_c;
    _EL_U_237 = _x__EL_U_237;
    follower0_c = _x_follower0_c;
    _EL_U_239 = _x__EL_U_239;
    follower0_dist = _x_follower0_dist;

  }
}
