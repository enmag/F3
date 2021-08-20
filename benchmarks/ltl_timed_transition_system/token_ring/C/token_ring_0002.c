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
bool _J328, _x__J328;
bool _J322, _x__J322;
bool _J315, _x__J315;
bool _J309, _x__J309;
bool _J301, _x__J301;
bool _J295, _x__J295;
bool _EL_U_254, _x__EL_U_254;
bool _EL_U_256, _x__EL_U_256;
bool _EL_X_221, _x__EL_X_221;
bool _EL_U_258, _x__EL_U_258;
bool _EL_U_260, _x__EL_U_260;
bool _EL_U_262, _x__EL_U_262;
bool _EL_U_264, _x__EL_U_264;

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
  _J328 = __VERIFIER_nondet_bool();
  _J322 = __VERIFIER_nondet_bool();
  _J315 = __VERIFIER_nondet_bool();
  _J309 = __VERIFIER_nondet_bool();
  _J301 = __VERIFIER_nondet_bool();
  _J295 = __VERIFIER_nondet_bool();
  _EL_U_254 = __VERIFIER_nondet_bool();
  _EL_U_256 = __VERIFIER_nondet_bool();
  _EL_X_221 = __VERIFIER_nondet_bool();
  _EL_U_258 = __VERIFIER_nondet_bool();
  _EL_U_260 = __VERIFIER_nondet_bool();
  _EL_U_262 = __VERIFIER_nondet_bool();
  _EL_U_264 = __VERIFIER_nondet_bool();

  bool __ok = (((((st1_l && ((st1_evt1 && ( !st1_evt0)) || ((( !st1_evt0) && ( !st1_evt1)) || (st1_evt0 && ( !st1_evt1))))) && ( !(st1_req_time <= 0.0))) && (((st0_l && ((st0_evt1 && ( !st0_evt0)) || ((( !st0_evt0) && ( !st0_evt1)) || (st0_evt0 && ( !st0_evt1))))) && ( !(st0_req_time <= 0.0))) && ((((mgr_l && ((mgr_evt1 && ( !mgr_evt0)) || ((( !mgr_evt0) && ( !mgr_evt1)) || (mgr_evt0 && ( !mgr_evt1))))) && ((mgr_c == 0.0) && (mgr_timeout == 0.0))) && (mgr_l || (mgr_c <= mgr_timeout))) && ((tot_transm_time == 0.0) && (0.0 <= delta))))) && (delta == _diverge_delta)) && ((((((( !((( !(_EL_U_264 || ( !(( !(10.0 <= tot_transm_time)) || _EL_U_262)))) || (_EL_U_260 || ( !(_EL_U_258 || (( !mgr_l) && _EL_X_221))))) || (_EL_U_256 || ( !((1.0 <= _diverge_delta) || _EL_U_254))))) && ( !_J295)) && ( !_J301)) && ( !_J309)) && ( !_J315)) && ( !_J322)) && ( !_J328)));
  while (__steps_to_fair >= 0 && __ok) {
    if ((((((_J295 && _J301) && _J309) && _J315) && _J322) && _J328)) {
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
    _x__J328 = __VERIFIER_nondet_bool();
    _x__J322 = __VERIFIER_nondet_bool();
    _x__J315 = __VERIFIER_nondet_bool();
    _x__J309 = __VERIFIER_nondet_bool();
    _x__J301 = __VERIFIER_nondet_bool();
    _x__J295 = __VERIFIER_nondet_bool();
    _x__EL_U_254 = __VERIFIER_nondet_bool();
    _x__EL_U_256 = __VERIFIER_nondet_bool();
    _x__EL_X_221 = __VERIFIER_nondet_bool();
    _x__EL_U_258 = __VERIFIER_nondet_bool();
    _x__EL_U_260 = __VERIFIER_nondet_bool();
    _x__EL_U_262 = __VERIFIER_nondet_bool();
    _x__EL_U_264 = __VERIFIER_nondet_bool();

    __ok = (((((((((_x_st1_evt1 && ( !_x_st1_evt0)) || ((( !_x_st1_evt0) && ( !_x_st1_evt1)) || (_x_st1_evt0 && ( !_x_st1_evt1)))) && ( !(_x_st1_req_time <= 0.0))) && (((st1_l == _x_st1_l) && (st1_req_time == _x_st1_req_time)) || ( !(( !(delta <= 0.0)) || (st1_evt1 && ( !st1_evt0)))))) && ((((( !st1_evt0) && ( !st1_evt1)) && ( !_x_st1_l)) && ((st1_req_time == _x_st1_req_time) && (_x_mgr_timeout == st1_req_time))) || ( !(st1_l && ((delta == 0.0) && ((( !st1_evt0) && ( !st1_evt1)) || (st1_evt0 && ( !st1_evt1)))))))) && (((st1_evt0 && ( !st1_evt1)) && (( !(mgr_c <= 0.0)) && _x_st1_l)) || ( !(( !st1_l) && ((delta == 0.0) && ((( !st1_evt0) && ( !st1_evt1)) || (st1_evt0 && ( !st1_evt1)))))))) && (((((((_x_st0_evt1 && ( !_x_st0_evt0)) || ((( !_x_st0_evt0) && ( !_x_st0_evt1)) || (_x_st0_evt0 && ( !_x_st0_evt1)))) && ( !(_x_st0_req_time <= 0.0))) && (((st0_l == _x_st0_l) && (st0_req_time == _x_st0_req_time)) || ( !(( !(delta <= 0.0)) || (st0_evt1 && ( !st0_evt0)))))) && ((((( !st0_evt0) && ( !st0_evt1)) && ( !_x_st0_l)) && ((st0_req_time == _x_st0_req_time) && (_x_mgr_timeout == st0_req_time))) || ( !(st0_l && ((delta == 0.0) && ((( !st0_evt0) && ( !st0_evt1)) || (st0_evt0 && ( !st0_evt1)))))))) && (((st0_evt0 && ( !st0_evt1)) && (_x_st0_l && ( !(mgr_c <= 0.0)))) || ( !(( !st0_l) && ((delta == 0.0) && ((( !st0_evt0) && ( !st0_evt1)) || (st0_evt0 && ( !st0_evt1)))))))) && (((((((_x_mgr_evt1 && ( !_x_mgr_evt0)) || ((( !_x_mgr_evt0) && ( !_x_mgr_evt1)) || (_x_mgr_evt0 && ( !_x_mgr_evt1)))) && (_x_mgr_l || (_x_mgr_c <= _x_mgr_timeout))) && ((((mgr_l == _x_mgr_l) && ((delta + (mgr_c + (-1.0 * _x_mgr_c))) == 0.0)) && (mgr_timeout == _x_mgr_timeout)) || ( !((mgr_evt1 && ( !mgr_evt0)) || ( !(delta <= 0.0)))))) && (((( !mgr_evt0) && ( !mgr_evt1)) && (( !_x_mgr_l) && (_x_mgr_c == 0.0))) || ( !(mgr_l && (((( !mgr_evt0) && ( !mgr_evt1)) || (mgr_evt0 && ( !mgr_evt1))) && (delta == 0.0)))))) && (((_x_mgr_l && (mgr_evt0 && ( !mgr_evt1))) && ((_x_mgr_c == 0.0) && (_x_mgr_timeout == 0.0))) || ( !(( !mgr_l) && (((( !mgr_evt0) && ( !mgr_evt1)) || (mgr_evt0 && ( !mgr_evt1))) && (delta == 0.0)))))) && ((((((0.0 <= _x_delta) && ((st0_evt1 && ( !st0_evt0)) || (st1_evt1 && ( !st1_evt0)))) && ((( !mgr_evt0) && ( !mgr_evt1)) == ((( !st0_evt0) && ( !st0_evt1)) || (( !st1_evt0) && ( !st1_evt1))))) && ((mgr_evt0 && ( !mgr_evt1)) == ((st0_evt0 && ( !st0_evt1)) || (st1_evt0 && ( !st1_evt1))))) && (((tot_transm_time + ((-1.0 * _x_tot_transm_time) + mgr_c)) == 0.0) || ( !(_x_mgr_l && ( !mgr_l))))) && ((_x_mgr_l && ( !mgr_l)) || (tot_transm_time == _x_tot_transm_time)))))) && (((delta == _x__diverge_delta) || ( !(1.0 <= _diverge_delta))) && ((1.0 <= _diverge_delta) || ((delta + (_diverge_delta + (-1.0 * _x__diverge_delta))) == 0.0)))) && ((((((((_EL_U_256 == (_x__EL_U_256 || ( !(_x__EL_U_254 || (1.0 <= _x__diverge_delta))))) && ((_EL_U_254 == (_x__EL_U_254 || (1.0 <= _x__diverge_delta))) && ((_EL_U_260 == (_x__EL_U_260 || ( !(_x__EL_U_258 || (( !_x_mgr_l) && _x__EL_X_221))))) && ((_EL_U_258 == (_x__EL_U_258 || (( !_x_mgr_l) && _x__EL_X_221))) && ((_x_mgr_l == _EL_X_221) && ((_EL_U_262 == (_x__EL_U_262 || ( !(10.0 <= _x_tot_transm_time)))) && (_EL_U_264 == (_x__EL_U_264 || ( !(_x__EL_U_262 || ( !(10.0 <= _x_tot_transm_time)))))))))))) && (_x__J295 == (( !(((((_J295 && _J301) && _J309) && _J315) && _J322) && _J328)) && ((((((_J295 && _J301) && _J309) && _J315) && _J322) && _J328) || ((( !(10.0 <= tot_transm_time)) || ( !(( !(10.0 <= tot_transm_time)) || _EL_U_262))) || _J295))))) && (_x__J301 == (( !(((((_J295 && _J301) && _J309) && _J315) && _J322) && _J328)) && ((((((_J295 && _J301) && _J309) && _J315) && _J322) && _J328) || ((( !(( !(10.0 <= tot_transm_time)) || _EL_U_262)) || ( !(_EL_U_264 || ( !(( !(10.0 <= tot_transm_time)) || _EL_U_262))))) || _J301))))) && (_x__J309 == (( !(((((_J295 && _J301) && _J309) && _J315) && _J322) && _J328)) && ((((((_J295 && _J301) && _J309) && _J315) && _J322) && _J328) || (((( !mgr_l) && _EL_X_221) || ( !(_EL_U_258 || (( !mgr_l) && _EL_X_221)))) || _J309))))) && (_x__J315 == (( !(((((_J295 && _J301) && _J309) && _J315) && _J322) && _J328)) && ((((((_J295 && _J301) && _J309) && _J315) && _J322) && _J328) || ((( !(_EL_U_258 || (( !mgr_l) && _EL_X_221))) || ( !(_EL_U_260 || ( !(_EL_U_258 || (( !mgr_l) && _EL_X_221)))))) || _J315))))) && (_x__J322 == (( !(((((_J295 && _J301) && _J309) && _J315) && _J322) && _J328)) && ((((((_J295 && _J301) && _J309) && _J315) && _J322) && _J328) || (((1.0 <= _diverge_delta) || ( !((1.0 <= _diverge_delta) || _EL_U_254))) || _J322))))) && (_x__J328 == (( !(((((_J295 && _J301) && _J309) && _J315) && _J322) && _J328)) && ((((((_J295 && _J301) && _J309) && _J315) && _J322) && _J328) || ((( !((1.0 <= _diverge_delta) || _EL_U_254)) || ( !(_EL_U_256 || ( !((1.0 <= _diverge_delta) || _EL_U_254))))) || _J328))))));
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
    _J328 = _x__J328;
    _J322 = _x__J322;
    _J315 = _x__J315;
    _J309 = _x__J309;
    _J301 = _x__J301;
    _J295 = _x__J295;
    _EL_U_254 = _x__EL_U_254;
    _EL_U_256 = _x__EL_U_256;
    _EL_X_221 = _x__EL_X_221;
    _EL_U_258 = _x__EL_U_258;
    _EL_U_260 = _x__EL_U_260;
    _EL_U_262 = _x__EL_U_262;
    _EL_U_264 = _x__EL_U_264;

  }
}
