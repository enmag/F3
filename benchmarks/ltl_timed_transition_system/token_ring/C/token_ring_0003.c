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
float tot_transm_time, _x_tot_transm_time;
float mgr_timeout, _x_mgr_timeout;
float mgr_c, _x_mgr_c;
bool mgr_l, _x_mgr_l;
bool mgr_evt1, _x_mgr_evt1;
bool mgr_evt0, _x_mgr_evt0;
float st0_req_time, _x_st0_req_time;
bool st0_evt1, _x_st0_evt1;
bool st0_evt0, _x_st0_evt0;
bool st0_l, _x_st0_l;
float st1_req_time, _x_st1_req_time;
bool st1_evt1, _x_st1_evt1;
bool st1_evt0, _x_st1_evt0;
bool st1_l, _x_st1_l;
float st2_req_time, _x_st2_req_time;
bool st2_evt1, _x_st2_evt1;
bool st2_evt0, _x_st2_evt0;
bool st2_l, _x_st2_l;
bool _J389, _x__J389;
bool _J383, _x__J383;
bool _J376, _x__J376;
bool _J370, _x__J370;
bool _J362, _x__J362;
bool _J356, _x__J356;
bool _EL_U_315, _x__EL_U_315;
bool _EL_U_317, _x__EL_U_317;
bool _EL_X_282, _x__EL_X_282;
bool _EL_U_319, _x__EL_U_319;
bool _EL_U_321, _x__EL_U_321;
bool _EL_U_323, _x__EL_U_323;
bool _EL_U_325, _x__EL_U_325;

  int __steps_to_fair = __VERIFIER_nondet_int();
  _diverge_delta = __VERIFIER_nondet_float();
  delta = __VERIFIER_nondet_float();
  tot_transm_time = __VERIFIER_nondet_float();
  mgr_timeout = __VERIFIER_nondet_float();
  mgr_c = __VERIFIER_nondet_float();
  mgr_l = __VERIFIER_nondet_bool();
  mgr_evt1 = __VERIFIER_nondet_bool();
  mgr_evt0 = __VERIFIER_nondet_bool();
  st0_req_time = __VERIFIER_nondet_float();
  st0_evt1 = __VERIFIER_nondet_bool();
  st0_evt0 = __VERIFIER_nondet_bool();
  st0_l = __VERIFIER_nondet_bool();
  st1_req_time = __VERIFIER_nondet_float();
  st1_evt1 = __VERIFIER_nondet_bool();
  st1_evt0 = __VERIFIER_nondet_bool();
  st1_l = __VERIFIER_nondet_bool();
  st2_req_time = __VERIFIER_nondet_float();
  st2_evt1 = __VERIFIER_nondet_bool();
  st2_evt0 = __VERIFIER_nondet_bool();
  st2_l = __VERIFIER_nondet_bool();
  _J389 = __VERIFIER_nondet_bool();
  _J383 = __VERIFIER_nondet_bool();
  _J376 = __VERIFIER_nondet_bool();
  _J370 = __VERIFIER_nondet_bool();
  _J362 = __VERIFIER_nondet_bool();
  _J356 = __VERIFIER_nondet_bool();
  _EL_U_315 = __VERIFIER_nondet_bool();
  _EL_U_317 = __VERIFIER_nondet_bool();
  _EL_X_282 = __VERIFIER_nondet_bool();
  _EL_U_319 = __VERIFIER_nondet_bool();
  _EL_U_321 = __VERIFIER_nondet_bool();
  _EL_U_323 = __VERIFIER_nondet_bool();
  _EL_U_325 = __VERIFIER_nondet_bool();

  bool __ok = (((((st2_l && ((st2_evt1 && ( !st2_evt0)) || ((( !st2_evt0) && ( !st2_evt1)) || (st2_evt0 && ( !st2_evt1))))) && ( !(st2_req_time <= 0.0))) && (((st1_l && ((st1_evt1 && ( !st1_evt0)) || ((( !st1_evt0) && ( !st1_evt1)) || (st1_evt0 && ( !st1_evt1))))) && ( !(st1_req_time <= 0.0))) && (((st0_l && ((st0_evt1 && ( !st0_evt0)) || ((( !st0_evt0) && ( !st0_evt1)) || (st0_evt0 && ( !st0_evt1))))) && ( !(st0_req_time <= 0.0))) && ((((mgr_l && ((mgr_evt1 && ( !mgr_evt0)) || ((( !mgr_evt0) && ( !mgr_evt1)) || (mgr_evt0 && ( !mgr_evt1))))) && ((mgr_c == 0.0) && (mgr_timeout == 0.0))) && (mgr_l || (mgr_c <= mgr_timeout))) && ((tot_transm_time == 0.0) && (0.0 <= delta)))))) && (delta == _diverge_delta)) && ((((((( !((( !(_EL_U_325 || ( !(( !(10.0 <= tot_transm_time)) || _EL_U_323)))) || (_EL_U_321 || ( !(_EL_U_319 || (( !mgr_l) && _EL_X_282))))) || (_EL_U_317 || ( !((1.0 <= _diverge_delta) || _EL_U_315))))) && ( !_J356)) && ( !_J362)) && ( !_J370)) && ( !_J376)) && ( !_J383)) && ( !_J389)));
  while (__steps_to_fair >= 0 && __ok) {
    if ((((((_J356 && _J362) && _J370) && _J376) && _J383) && _J389)) {
      __steps_to_fair = __VERIFIER_nondet_int();
    } else {
      __steps_to_fair--;
    }
    _x__diverge_delta = __VERIFIER_nondet_float();
    _x_delta = __VERIFIER_nondet_float();
    _x_tot_transm_time = __VERIFIER_nondet_float();
    _x_mgr_timeout = __VERIFIER_nondet_float();
    _x_mgr_c = __VERIFIER_nondet_float();
    _x_mgr_l = __VERIFIER_nondet_bool();
    _x_mgr_evt1 = __VERIFIER_nondet_bool();
    _x_mgr_evt0 = __VERIFIER_nondet_bool();
    _x_st0_req_time = __VERIFIER_nondet_float();
    _x_st0_evt1 = __VERIFIER_nondet_bool();
    _x_st0_evt0 = __VERIFIER_nondet_bool();
    _x_st0_l = __VERIFIER_nondet_bool();
    _x_st1_req_time = __VERIFIER_nondet_float();
    _x_st1_evt1 = __VERIFIER_nondet_bool();
    _x_st1_evt0 = __VERIFIER_nondet_bool();
    _x_st1_l = __VERIFIER_nondet_bool();
    _x_st2_req_time = __VERIFIER_nondet_float();
    _x_st2_evt1 = __VERIFIER_nondet_bool();
    _x_st2_evt0 = __VERIFIER_nondet_bool();
    _x_st2_l = __VERIFIER_nondet_bool();
    _x__J389 = __VERIFIER_nondet_bool();
    _x__J383 = __VERIFIER_nondet_bool();
    _x__J376 = __VERIFIER_nondet_bool();
    _x__J370 = __VERIFIER_nondet_bool();
    _x__J362 = __VERIFIER_nondet_bool();
    _x__J356 = __VERIFIER_nondet_bool();
    _x__EL_U_315 = __VERIFIER_nondet_bool();
    _x__EL_U_317 = __VERIFIER_nondet_bool();
    _x__EL_X_282 = __VERIFIER_nondet_bool();
    _x__EL_U_319 = __VERIFIER_nondet_bool();
    _x__EL_U_321 = __VERIFIER_nondet_bool();
    _x__EL_U_323 = __VERIFIER_nondet_bool();
    _x__EL_U_325 = __VERIFIER_nondet_bool();

    __ok = (((((((((_x_st2_evt1 && ( !_x_st2_evt0)) || ((( !_x_st2_evt0) && ( !_x_st2_evt1)) || (_x_st2_evt0 && ( !_x_st2_evt1)))) && ( !(_x_st2_req_time <= 0.0))) && (((st2_l == _x_st2_l) && (st2_req_time == _x_st2_req_time)) || ( !(( !(delta <= 0.0)) || (st2_evt1 && ( !st2_evt0)))))) && ((((( !st2_evt0) && ( !st2_evt1)) && ( !_x_st2_l)) && ((st2_req_time == _x_st2_req_time) && (_x_mgr_timeout == st2_req_time))) || ( !(st2_l && ((delta == 0.0) && ((( !st2_evt0) && ( !st2_evt1)) || (st2_evt0 && ( !st2_evt1)))))))) && (((st2_evt0 && ( !st2_evt1)) && (( !(mgr_c <= 0.0)) && _x_st2_l)) || ( !(( !st2_l) && ((delta == 0.0) && ((( !st2_evt0) && ( !st2_evt1)) || (st2_evt0 && ( !st2_evt1)))))))) && (((((((_x_st1_evt1 && ( !_x_st1_evt0)) || ((( !_x_st1_evt0) && ( !_x_st1_evt1)) || (_x_st1_evt0 && ( !_x_st1_evt1)))) && ( !(_x_st1_req_time <= 0.0))) && (((st1_l == _x_st1_l) && (st1_req_time == _x_st1_req_time)) || ( !(( !(delta <= 0.0)) || (st1_evt1 && ( !st1_evt0)))))) && ((((( !st1_evt0) && ( !st1_evt1)) && ( !_x_st1_l)) && ((st1_req_time == _x_st1_req_time) && (_x_mgr_timeout == st1_req_time))) || ( !(st1_l && ((delta == 0.0) && ((( !st1_evt0) && ( !st1_evt1)) || (st1_evt0 && ( !st1_evt1)))))))) && (((st1_evt0 && ( !st1_evt1)) && (( !(mgr_c <= 0.0)) && _x_st1_l)) || ( !(( !st1_l) && ((delta == 0.0) && ((( !st1_evt0) && ( !st1_evt1)) || (st1_evt0 && ( !st1_evt1)))))))) && (((((((_x_st0_evt1 && ( !_x_st0_evt0)) || ((( !_x_st0_evt0) && ( !_x_st0_evt1)) || (_x_st0_evt0 && ( !_x_st0_evt1)))) && ( !(_x_st0_req_time <= 0.0))) && (((st0_l == _x_st0_l) && (st0_req_time == _x_st0_req_time)) || ( !(( !(delta <= 0.0)) || (st0_evt1 && ( !st0_evt0)))))) && ((((( !st0_evt0) && ( !st0_evt1)) && ( !_x_st0_l)) && ((st0_req_time == _x_st0_req_time) && (_x_mgr_timeout == st0_req_time))) || ( !(st0_l && ((delta == 0.0) && ((( !st0_evt0) && ( !st0_evt1)) || (st0_evt0 && ( !st0_evt1)))))))) && (((st0_evt0 && ( !st0_evt1)) && (_x_st0_l && ( !(mgr_c <= 0.0)))) || ( !(( !st0_l) && ((delta == 0.0) && ((( !st0_evt0) && ( !st0_evt1)) || (st0_evt0 && ( !st0_evt1)))))))) && (((((((_x_mgr_evt1 && ( !_x_mgr_evt0)) || ((( !_x_mgr_evt0) && ( !_x_mgr_evt1)) || (_x_mgr_evt0 && ( !_x_mgr_evt1)))) && (_x_mgr_l || (_x_mgr_c <= _x_mgr_timeout))) && ((((mgr_l == _x_mgr_l) && ((delta + (mgr_c + (-1.0 * _x_mgr_c))) == 0.0)) && (mgr_timeout == _x_mgr_timeout)) || ( !((mgr_evt1 && ( !mgr_evt0)) || ( !(delta <= 0.0)))))) && (((( !mgr_evt0) && ( !mgr_evt1)) && (( !_x_mgr_l) && (_x_mgr_c == 0.0))) || ( !(mgr_l && (((( !mgr_evt0) && ( !mgr_evt1)) || (mgr_evt0 && ( !mgr_evt1))) && (delta == 0.0)))))) && (((_x_mgr_l && (mgr_evt0 && ( !mgr_evt1))) && ((_x_mgr_c == 0.0) && (_x_mgr_timeout == 0.0))) || ( !(( !mgr_l) && (((( !mgr_evt0) && ( !mgr_evt1)) || (mgr_evt0 && ( !mgr_evt1))) && (delta == 0.0)))))) && ((((((((0.0 <= _x_delta) && ((st0_evt1 && ( !st0_evt0)) || (st1_evt1 && ( !st1_evt0)))) && ((st0_evt1 && ( !st0_evt0)) || (st2_evt1 && ( !st2_evt0)))) && ((st1_evt1 && ( !st1_evt0)) || (st2_evt1 && ( !st2_evt0)))) && ((( !mgr_evt0) && ( !mgr_evt1)) == ((( !st2_evt0) && ( !st2_evt1)) || ((( !st0_evt0) && ( !st0_evt1)) || (( !st1_evt0) && ( !st1_evt1)))))) && ((mgr_evt0 && ( !mgr_evt1)) == ((st2_evt0 && ( !st2_evt1)) || ((st0_evt0 && ( !st0_evt1)) || (st1_evt0 && ( !st1_evt1)))))) && (((tot_transm_time + ((-1.0 * _x_tot_transm_time) + mgr_c)) == 0.0) || ( !(_x_mgr_l && ( !mgr_l))))) && ((_x_mgr_l && ( !mgr_l)) || (tot_transm_time == _x_tot_transm_time))))))) && (((delta == _x__diverge_delta) || ( !(1.0 <= _diverge_delta))) && ((1.0 <= _diverge_delta) || ((delta + (_diverge_delta + (-1.0 * _x__diverge_delta))) == 0.0)))) && ((((((((_EL_U_317 == (_x__EL_U_317 || ( !(_x__EL_U_315 || (1.0 <= _x__diverge_delta))))) && ((_EL_U_315 == (_x__EL_U_315 || (1.0 <= _x__diverge_delta))) && ((_EL_U_321 == (_x__EL_U_321 || ( !(_x__EL_U_319 || (( !_x_mgr_l) && _x__EL_X_282))))) && ((_EL_U_319 == (_x__EL_U_319 || (( !_x_mgr_l) && _x__EL_X_282))) && ((_x_mgr_l == _EL_X_282) && ((_EL_U_323 == (_x__EL_U_323 || ( !(10.0 <= _x_tot_transm_time)))) && (_EL_U_325 == (_x__EL_U_325 || ( !(_x__EL_U_323 || ( !(10.0 <= _x_tot_transm_time)))))))))))) && (_x__J356 == (( !(((((_J356 && _J362) && _J370) && _J376) && _J383) && _J389)) && ((((((_J356 && _J362) && _J370) && _J376) && _J383) && _J389) || ((( !(10.0 <= tot_transm_time)) || ( !(( !(10.0 <= tot_transm_time)) || _EL_U_323))) || _J356))))) && (_x__J362 == (( !(((((_J356 && _J362) && _J370) && _J376) && _J383) && _J389)) && ((((((_J356 && _J362) && _J370) && _J376) && _J383) && _J389) || ((( !(( !(10.0 <= tot_transm_time)) || _EL_U_323)) || ( !(_EL_U_325 || ( !(( !(10.0 <= tot_transm_time)) || _EL_U_323))))) || _J362))))) && (_x__J370 == (( !(((((_J356 && _J362) && _J370) && _J376) && _J383) && _J389)) && ((((((_J356 && _J362) && _J370) && _J376) && _J383) && _J389) || (((( !mgr_l) && _EL_X_282) || ( !(_EL_U_319 || (( !mgr_l) && _EL_X_282)))) || _J370))))) && (_x__J376 == (( !(((((_J356 && _J362) && _J370) && _J376) && _J383) && _J389)) && ((((((_J356 && _J362) && _J370) && _J376) && _J383) && _J389) || ((( !(_EL_U_319 || (( !mgr_l) && _EL_X_282))) || ( !(_EL_U_321 || ( !(_EL_U_319 || (( !mgr_l) && _EL_X_282)))))) || _J376))))) && (_x__J383 == (( !(((((_J356 && _J362) && _J370) && _J376) && _J383) && _J389)) && ((((((_J356 && _J362) && _J370) && _J376) && _J383) && _J389) || (((1.0 <= _diverge_delta) || ( !((1.0 <= _diverge_delta) || _EL_U_315))) || _J383))))) && (_x__J389 == (( !(((((_J356 && _J362) && _J370) && _J376) && _J383) && _J389)) && ((((((_J356 && _J362) && _J370) && _J376) && _J383) && _J389) || ((( !((1.0 <= _diverge_delta) || _EL_U_315)) || ( !(_EL_U_317 || ( !((1.0 <= _diverge_delta) || _EL_U_315))))) || _J389))))));
    _diverge_delta = _x__diverge_delta;
    delta = _x_delta;
    tot_transm_time = _x_tot_transm_time;
    mgr_timeout = _x_mgr_timeout;
    mgr_c = _x_mgr_c;
    mgr_l = _x_mgr_l;
    mgr_evt1 = _x_mgr_evt1;
    mgr_evt0 = _x_mgr_evt0;
    st0_req_time = _x_st0_req_time;
    st0_evt1 = _x_st0_evt1;
    st0_evt0 = _x_st0_evt0;
    st0_l = _x_st0_l;
    st1_req_time = _x_st1_req_time;
    st1_evt1 = _x_st1_evt1;
    st1_evt0 = _x_st1_evt0;
    st1_l = _x_st1_l;
    st2_req_time = _x_st2_req_time;
    st2_evt1 = _x_st2_evt1;
    st2_evt0 = _x_st2_evt0;
    st2_l = _x_st2_l;
    _J389 = _x__J389;
    _J383 = _x__J383;
    _J376 = _x__J376;
    _J370 = _x__J370;
    _J362 = _x__J362;
    _J356 = _x__J356;
    _EL_U_315 = _x__EL_U_315;
    _EL_U_317 = _x__EL_U_317;
    _EL_X_282 = _x__EL_X_282;
    _EL_U_319 = _x__EL_U_319;
    _EL_U_321 = _x__EL_U_321;
    _EL_U_323 = _x__EL_U_323;
    _EL_U_325 = _x__EL_U_325;

  }
}
