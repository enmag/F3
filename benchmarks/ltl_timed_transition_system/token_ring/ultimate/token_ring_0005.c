//@ ltl invariant negative: ( ( ([] (<> (! AP((10.0 <= tot_transm_time))))) || (! ([] (<> ( (! AP((mgr_l != 0))) && (X AP((mgr_l != 0)))))))) || (! ([] (<> AP((1.0 <= _diverge_delta))))));

extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);

char __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}


float _diverge_delta, _x__diverge_delta;
char st4_evt1, _x_st4_evt1;
float st4_req_time, _x_st4_req_time;
char st4_l, _x_st4_l;
char st2_evt1, _x_st2_evt1;
char st2_evt0, _x_st2_evt0;
float st2_req_time, _x_st2_req_time;
char st2_l, _x_st2_l;
char st1_evt1, _x_st1_evt1;
char st1_evt0, _x_st1_evt0;
float delta, _x_delta;
char st1_l, _x_st1_l;
float tot_transm_time, _x_tot_transm_time;
char st3_l, _x_st3_l;
float st0_req_time, _x_st0_req_time;
char mgr_l, _x_mgr_l;
float st3_req_time, _x_st3_req_time;
float mgr_c, _x_mgr_c;
float mgr_timeout, _x_mgr_timeout;
char st3_evt0, _x_st3_evt0;
char mgr_evt0, _x_mgr_evt0;
char st3_evt1, _x_st3_evt1;
char mgr_evt1, _x_mgr_evt1;
char st0_l, _x_st0_l;
char st0_evt0, _x_st0_evt0;
char st0_evt1, _x_st0_evt1;
char st4_evt0, _x_st4_evt0;
float st1_req_time, _x_st1_req_time;

int main()
{
  _diverge_delta = __VERIFIER_nondet_float();
  st4_evt1 = __VERIFIER_nondet_bool();
  st4_req_time = __VERIFIER_nondet_float();
  st4_l = __VERIFIER_nondet_bool();
  st2_evt1 = __VERIFIER_nondet_bool();
  st2_evt0 = __VERIFIER_nondet_bool();
  st2_req_time = __VERIFIER_nondet_float();
  st2_l = __VERIFIER_nondet_bool();
  st1_evt1 = __VERIFIER_nondet_bool();
  st1_evt0 = __VERIFIER_nondet_bool();
  delta = __VERIFIER_nondet_float();
  st1_l = __VERIFIER_nondet_bool();
  tot_transm_time = __VERIFIER_nondet_float();
  st3_l = __VERIFIER_nondet_bool();
  st0_req_time = __VERIFIER_nondet_float();
  mgr_l = __VERIFIER_nondet_bool();
  st3_req_time = __VERIFIER_nondet_float();
  mgr_c = __VERIFIER_nondet_float();
  mgr_timeout = __VERIFIER_nondet_float();
  st3_evt0 = __VERIFIER_nondet_bool();
  mgr_evt0 = __VERIFIER_nondet_bool();
  st3_evt1 = __VERIFIER_nondet_bool();
  mgr_evt1 = __VERIFIER_nondet_bool();
  st0_l = __VERIFIER_nondet_bool();
  st0_evt0 = __VERIFIER_nondet_bool();
  st0_evt1 = __VERIFIER_nondet_bool();
  st4_evt0 = __VERIFIER_nondet_bool();
  st1_req_time = __VERIFIER_nondet_float();

  int __ok = (((((st4_l != 0) && (((st4_evt1 != 0) && ( !(st4_evt0 != 0))) || ((( !(st4_evt0 != 0)) && ( !(st4_evt1 != 0))) || ((st4_evt0 != 0) && ( !(st4_evt1 != 0)))))) && ( !(st4_req_time <= 0.0))) && ((((st3_l != 0) && (((st3_evt1 != 0) && ( !(st3_evt0 != 0))) || ((( !(st3_evt0 != 0)) && ( !(st3_evt1 != 0))) || ((st3_evt0 != 0) && ( !(st3_evt1 != 0)))))) && ( !(st3_req_time <= 0.0))) && ((((st2_l != 0) && (((st2_evt1 != 0) && ( !(st2_evt0 != 0))) || ((( !(st2_evt0 != 0)) && ( !(st2_evt1 != 0))) || ((st2_evt0 != 0) && ( !(st2_evt1 != 0)))))) && ( !(st2_req_time <= 0.0))) && ((((st1_l != 0) && (((st1_evt1 != 0) && ( !(st1_evt0 != 0))) || ((( !(st1_evt0 != 0)) && ( !(st1_evt1 != 0))) || ((st1_evt0 != 0) && ( !(st1_evt1 != 0)))))) && ( !(st1_req_time <= 0.0))) && ((((st0_l != 0) && (((st0_evt1 != 0) && ( !(st0_evt0 != 0))) || ((( !(st0_evt0 != 0)) && ( !(st0_evt1 != 0))) || ((st0_evt0 != 0) && ( !(st0_evt1 != 0)))))) && ( !(st0_req_time <= 0.0))) && (((((mgr_l != 0) && (((mgr_evt1 != 0) && ( !(mgr_evt0 != 0))) || ((( !(mgr_evt0 != 0)) && ( !(mgr_evt1 != 0))) || ((mgr_evt0 != 0) && ( !(mgr_evt1 != 0)))))) && ((mgr_c == 0.0) && (mgr_timeout == 0.0))) && ((mgr_l != 0) || (mgr_c <= mgr_timeout))) && ((tot_transm_time == 0.0) && (0.0 <= delta)))))))) && (delta == _diverge_delta));
  while (__ok) {
    _x__diverge_delta = __VERIFIER_nondet_float();
    _x_st4_evt1 = __VERIFIER_nondet_bool();
    _x_st4_req_time = __VERIFIER_nondet_float();
    _x_st4_l = __VERIFIER_nondet_bool();
    _x_st2_evt1 = __VERIFIER_nondet_bool();
    _x_st2_evt0 = __VERIFIER_nondet_bool();
    _x_st2_req_time = __VERIFIER_nondet_float();
    _x_st2_l = __VERIFIER_nondet_bool();
    _x_st1_evt1 = __VERIFIER_nondet_bool();
    _x_st1_evt0 = __VERIFIER_nondet_bool();
    _x_delta = __VERIFIER_nondet_float();
    _x_st1_l = __VERIFIER_nondet_bool();
    _x_tot_transm_time = __VERIFIER_nondet_float();
    _x_st3_l = __VERIFIER_nondet_bool();
    _x_st0_req_time = __VERIFIER_nondet_float();
    _x_mgr_l = __VERIFIER_nondet_bool();
    _x_st3_req_time = __VERIFIER_nondet_float();
    _x_mgr_c = __VERIFIER_nondet_float();
    _x_mgr_timeout = __VERIFIER_nondet_float();
    _x_st3_evt0 = __VERIFIER_nondet_bool();
    _x_mgr_evt0 = __VERIFIER_nondet_bool();
    _x_st3_evt1 = __VERIFIER_nondet_bool();
    _x_mgr_evt1 = __VERIFIER_nondet_bool();
    _x_st0_l = __VERIFIER_nondet_bool();
    _x_st0_evt0 = __VERIFIER_nondet_bool();
    _x_st0_evt1 = __VERIFIER_nondet_bool();
    _x_st4_evt0 = __VERIFIER_nondet_bool();
    _x_st1_req_time = __VERIFIER_nondet_float();

    __ok = (((((((((_x_st4_evt1 != 0) && ( !(_x_st4_evt0 != 0))) || ((( !(_x_st4_evt0 != 0)) && ( !(_x_st4_evt1 != 0))) || ((_x_st4_evt0 != 0) && ( !(_x_st4_evt1 != 0))))) && ( !(_x_st4_req_time <= 0.0))) && ((((st4_l != 0) == (_x_st4_l != 0)) && (st4_req_time == _x_st4_req_time)) || ( !(( !(delta <= 0.0)) || ((st4_evt1 != 0) && ( !(st4_evt0 != 0))))))) && ((((( !(st4_evt0 != 0)) && ( !(st4_evt1 != 0))) && ( !(_x_st4_l != 0))) && ((st4_req_time == _x_st4_req_time) && (_x_mgr_timeout == st4_req_time))) || ( !((st4_l != 0) && ((delta == 0.0) && ((( !(st4_evt0 != 0)) && ( !(st4_evt1 != 0))) || ((st4_evt0 != 0) && ( !(st4_evt1 != 0))))))))) && ((((st4_evt0 != 0) && ( !(st4_evt1 != 0))) && (( !(mgr_c <= 0.0)) && (_x_st4_l != 0))) || ( !(( !(st4_l != 0)) && ((delta == 0.0) && ((( !(st4_evt0 != 0)) && ( !(st4_evt1 != 0))) || ((st4_evt0 != 0) && ( !(st4_evt1 != 0))))))))) && ((((((((_x_st3_evt1 != 0) && ( !(_x_st3_evt0 != 0))) || ((( !(_x_st3_evt0 != 0)) && ( !(_x_st3_evt1 != 0))) || ((_x_st3_evt0 != 0) && ( !(_x_st3_evt1 != 0))))) && ( !(_x_st3_req_time <= 0.0))) && ((((st3_l != 0) == (_x_st3_l != 0)) && (st3_req_time == _x_st3_req_time)) || ( !(( !(delta <= 0.0)) || ((st3_evt1 != 0) && ( !(st3_evt0 != 0))))))) && ((((( !(st3_evt0 != 0)) && ( !(st3_evt1 != 0))) && ( !(_x_st3_l != 0))) && ((st3_req_time == _x_st3_req_time) && (_x_mgr_timeout == st3_req_time))) || ( !((st3_l != 0) && ((delta == 0.0) && ((( !(st3_evt0 != 0)) && ( !(st3_evt1 != 0))) || ((st3_evt0 != 0) && ( !(st3_evt1 != 0))))))))) && ((((st3_evt0 != 0) && ( !(st3_evt1 != 0))) && (( !(mgr_c <= 0.0)) && (_x_st3_l != 0))) || ( !(( !(st3_l != 0)) && ((delta == 0.0) && ((( !(st3_evt0 != 0)) && ( !(st3_evt1 != 0))) || ((st3_evt0 != 0) && ( !(st3_evt1 != 0))))))))) && ((((((((_x_st2_evt1 != 0) && ( !(_x_st2_evt0 != 0))) || ((( !(_x_st2_evt0 != 0)) && ( !(_x_st2_evt1 != 0))) || ((_x_st2_evt0 != 0) && ( !(_x_st2_evt1 != 0))))) && ( !(_x_st2_req_time <= 0.0))) && ((((st2_l != 0) == (_x_st2_l != 0)) && (st2_req_time == _x_st2_req_time)) || ( !(( !(delta <= 0.0)) || ((st2_evt1 != 0) && ( !(st2_evt0 != 0))))))) && ((((( !(st2_evt0 != 0)) && ( !(st2_evt1 != 0))) && ( !(_x_st2_l != 0))) && ((st2_req_time == _x_st2_req_time) && (_x_mgr_timeout == st2_req_time))) || ( !((st2_l != 0) && ((delta == 0.0) && ((( !(st2_evt0 != 0)) && ( !(st2_evt1 != 0))) || ((st2_evt0 != 0) && ( !(st2_evt1 != 0))))))))) && ((((st2_evt0 != 0) && ( !(st2_evt1 != 0))) && (( !(mgr_c <= 0.0)) && (_x_st2_l != 0))) || ( !(( !(st2_l != 0)) && ((delta == 0.0) && ((( !(st2_evt0 != 0)) && ( !(st2_evt1 != 0))) || ((st2_evt0 != 0) && ( !(st2_evt1 != 0))))))))) && ((((((((_x_st1_evt1 != 0) && ( !(_x_st1_evt0 != 0))) || ((( !(_x_st1_evt0 != 0)) && ( !(_x_st1_evt1 != 0))) || ((_x_st1_evt0 != 0) && ( !(_x_st1_evt1 != 0))))) && ( !(_x_st1_req_time <= 0.0))) && ((((st1_l != 0) == (_x_st1_l != 0)) && (st1_req_time == _x_st1_req_time)) || ( !(( !(delta <= 0.0)) || ((st1_evt1 != 0) && ( !(st1_evt0 != 0))))))) && ((((( !(st1_evt0 != 0)) && ( !(st1_evt1 != 0))) && ( !(_x_st1_l != 0))) && ((st1_req_time == _x_st1_req_time) && (_x_mgr_timeout == st1_req_time))) || ( !((st1_l != 0) && ((delta == 0.0) && ((( !(st1_evt0 != 0)) && ( !(st1_evt1 != 0))) || ((st1_evt0 != 0) && ( !(st1_evt1 != 0))))))))) && ((((st1_evt0 != 0) && ( !(st1_evt1 != 0))) && (( !(mgr_c <= 0.0)) && (_x_st1_l != 0))) || ( !(( !(st1_l != 0)) && ((delta == 0.0) && ((( !(st1_evt0 != 0)) && ( !(st1_evt1 != 0))) || ((st1_evt0 != 0) && ( !(st1_evt1 != 0))))))))) && ((((((((_x_st0_evt1 != 0) && ( !(_x_st0_evt0 != 0))) || ((( !(_x_st0_evt0 != 0)) && ( !(_x_st0_evt1 != 0))) || ((_x_st0_evt0 != 0) && ( !(_x_st0_evt1 != 0))))) && ( !(_x_st0_req_time <= 0.0))) && ((((st0_l != 0) == (_x_st0_l != 0)) && (st0_req_time == _x_st0_req_time)) || ( !(( !(delta <= 0.0)) || ((st0_evt1 != 0) && ( !(st0_evt0 != 0))))))) && ((((( !(st0_evt0 != 0)) && ( !(st0_evt1 != 0))) && ( !(_x_st0_l != 0))) && ((st0_req_time == _x_st0_req_time) && (_x_mgr_timeout == st0_req_time))) || ( !((st0_l != 0) && ((delta == 0.0) && ((( !(st0_evt0 != 0)) && ( !(st0_evt1 != 0))) || ((st0_evt0 != 0) && ( !(st0_evt1 != 0))))))))) && ((((st0_evt0 != 0) && ( !(st0_evt1 != 0))) && ((_x_st0_l != 0) && ( !(mgr_c <= 0.0)))) || ( !(( !(st0_l != 0)) && ((delta == 0.0) && ((( !(st0_evt0 != 0)) && ( !(st0_evt1 != 0))) || ((st0_evt0 != 0) && ( !(st0_evt1 != 0))))))))) && ((((((((_x_mgr_evt1 != 0) && ( !(_x_mgr_evt0 != 0))) || ((( !(_x_mgr_evt0 != 0)) && ( !(_x_mgr_evt1 != 0))) || ((_x_mgr_evt0 != 0) && ( !(_x_mgr_evt1 != 0))))) && ((_x_mgr_l != 0) || (_x_mgr_c <= _x_mgr_timeout))) && (((((mgr_l != 0) == (_x_mgr_l != 0)) && ((delta + (mgr_c + (-1.0 * _x_mgr_c))) == 0.0)) && (mgr_timeout == _x_mgr_timeout)) || ( !(((mgr_evt1 != 0) && ( !(mgr_evt0 != 0))) || ( !(delta <= 0.0)))))) && (((( !(mgr_evt0 != 0)) && ( !(mgr_evt1 != 0))) && (( !(_x_mgr_l != 0)) && (_x_mgr_c == 0.0))) || ( !((mgr_l != 0) && (((( !(mgr_evt0 != 0)) && ( !(mgr_evt1 != 0))) || ((mgr_evt0 != 0) && ( !(mgr_evt1 != 0)))) && (delta == 0.0)))))) && ((((_x_mgr_l != 0) && ((mgr_evt0 != 0) && ( !(mgr_evt1 != 0)))) && ((_x_mgr_c == 0.0) && (_x_mgr_timeout == 0.0))) || ( !(( !(mgr_l != 0)) && (((( !(mgr_evt0 != 0)) && ( !(mgr_evt1 != 0))) || ((mgr_evt0 != 0) && ( !(mgr_evt1 != 0)))) && (delta == 0.0)))))) && (((((((((((((((0.0 <= _x_delta) && (((st0_evt1 != 0) && ( !(st0_evt0 != 0))) || ((st1_evt1 != 0) && ( !(st1_evt0 != 0))))) && (((st0_evt1 != 0) && ( !(st0_evt0 != 0))) || ((st2_evt1 != 0) && ( !(st2_evt0 != 0))))) && (((st0_evt1 != 0) && ( !(st0_evt0 != 0))) || ((st3_evt1 != 0) && ( !(st3_evt0 != 0))))) && (((st0_evt1 != 0) && ( !(st0_evt0 != 0))) || ((st4_evt1 != 0) && ( !(st4_evt0 != 0))))) && (((st1_evt1 != 0) && ( !(st1_evt0 != 0))) || ((st2_evt1 != 0) && ( !(st2_evt0 != 0))))) && (((st1_evt1 != 0) && ( !(st1_evt0 != 0))) || ((st3_evt1 != 0) && ( !(st3_evt0 != 0))))) && (((st1_evt1 != 0) && ( !(st1_evt0 != 0))) || ((st4_evt1 != 0) && ( !(st4_evt0 != 0))))) && (((st2_evt1 != 0) && ( !(st2_evt0 != 0))) || ((st3_evt1 != 0) && ( !(st3_evt0 != 0))))) && (((st2_evt1 != 0) && ( !(st2_evt0 != 0))) || ((st4_evt1 != 0) && ( !(st4_evt0 != 0))))) && (((st3_evt1 != 0) && ( !(st3_evt0 != 0))) || ((st4_evt1 != 0) && ( !(st4_evt0 != 0))))) && ((( !(mgr_evt0 != 0)) && ( !(mgr_evt1 != 0))) == ((( !(st4_evt0 != 0)) && ( !(st4_evt1 != 0))) || ((( !(st3_evt0 != 0)) && ( !(st3_evt1 != 0))) || ((( !(st2_evt0 != 0)) && ( !(st2_evt1 != 0))) || ((( !(st0_evt0 != 0)) && ( !(st0_evt1 != 0))) || (( !(st1_evt0 != 0)) && ( !(st1_evt1 != 0))))))))) && (((mgr_evt0 != 0) && ( !(mgr_evt1 != 0))) == (((st4_evt0 != 0) && ( !(st4_evt1 != 0))) || (((st3_evt0 != 0) && ( !(st3_evt1 != 0))) || (((st2_evt0 != 0) && ( !(st2_evt1 != 0))) || (((st0_evt0 != 0) && ( !(st0_evt1 != 0))) || ((st1_evt0 != 0) && ( !(st1_evt1 != 0))))))))) && (((tot_transm_time + ((-1.0 * _x_tot_transm_time) + mgr_c)) == 0.0) || ( !((_x_mgr_l != 0) && ( !(mgr_l != 0)))))) && (((_x_mgr_l != 0) && ( !(mgr_l != 0))) || (tot_transm_time == _x_tot_transm_time))))))))) && (((delta == _x__diverge_delta) || ( !(1.0 <= _diverge_delta))) && ((1.0 <= _diverge_delta) || ((delta + (_diverge_delta + (-1.0 * _x__diverge_delta))) == 0.0))));
    _diverge_delta = _x__diverge_delta;
    st4_evt1 = _x_st4_evt1;
    st4_req_time = _x_st4_req_time;
    st4_l = _x_st4_l;
    st2_evt1 = _x_st2_evt1;
    st2_evt0 = _x_st2_evt0;
    st2_req_time = _x_st2_req_time;
    st2_l = _x_st2_l;
    st1_evt1 = _x_st1_evt1;
    st1_evt0 = _x_st1_evt0;
    delta = _x_delta;
    st1_l = _x_st1_l;
    tot_transm_time = _x_tot_transm_time;
    st3_l = _x_st3_l;
    st0_req_time = _x_st0_req_time;
    mgr_l = _x_mgr_l;
    st3_req_time = _x_st3_req_time;
    mgr_c = _x_mgr_c;
    mgr_timeout = _x_mgr_timeout;
    st3_evt0 = _x_st3_evt0;
    mgr_evt0 = _x_mgr_evt0;
    st3_evt1 = _x_st3_evt1;
    mgr_evt1 = _x_mgr_evt1;
    st0_l = _x_st0_l;
    st0_evt0 = _x_st0_evt0;
    st0_evt1 = _x_st0_evt1;
    st4_evt0 = _x_st4_evt0;
    st1_req_time = _x_st1_req_time;

  }
}
