//@ ltl invariant negative: ( ( ([] (<> (! AP((10.0 <= tot_transm_time))))) || (! ([] (<> ( (! AP((mgr_l != 0))) && (X AP((mgr_l != 0)))))))) || (! ([] (<> AP((1.0 <= _diverge_delta))))));

extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);

char __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}


char st10_evt1, _x_st10_evt1;
float _diverge_delta, _x__diverge_delta;
char st10_evt0, _x_st10_evt0;
char st10_l, _x_st10_l;
char st9_evt1, _x_st9_evt1;
char st9_evt0, _x_st9_evt0;
char st9_l, _x_st9_l;
float st10_req_time, _x_st10_req_time;
char st8_evt1, _x_st8_evt1;
char st8_evt0, _x_st8_evt0;
char st8_l, _x_st8_l;
float st9_req_time, _x_st9_req_time;
char st7_evt1, _x_st7_evt1;
char st7_evt0, _x_st7_evt0;
char st7_l, _x_st7_l;
float st8_req_time, _x_st8_req_time;
char st6_evt1, _x_st6_evt1;
char st6_evt0, _x_st6_evt0;
char st6_l, _x_st6_l;
float st7_req_time, _x_st7_req_time;
char st5_evt1, _x_st5_evt1;
char st5_evt0, _x_st5_evt0;
float st1_req_time, _x_st1_req_time;
char st4_evt0, _x_st4_evt0;
char st0_evt0, _x_st0_evt0;
char st0_evt1, _x_st0_evt1;
float mgr_c, _x_mgr_c;
float st0_req_time, _x_st0_req_time;
char st3_evt0, _x_st3_evt0;
float tot_transm_time, _x_tot_transm_time;
char st1_l, _x_st1_l;
char st3_l, _x_st3_l;
float delta, _x_delta;
char st1_evt0, _x_st1_evt0;
char st0_l, _x_st0_l;
float st3_req_time, _x_st3_req_time;
char st1_evt1, _x_st1_evt1;
char mgr_evt0, _x_mgr_evt0;
char st2_l, _x_st2_l;
float mgr_timeout, _x_mgr_timeout;
float st2_req_time, _x_st2_req_time;
char mgr_evt1, _x_mgr_evt1;
char st2_evt0, _x_st2_evt0;
char st4_l, _x_st4_l;
char st2_evt1, _x_st2_evt1;
float st4_req_time, _x_st4_req_time;
float st6_req_time, _x_st6_req_time;
char st4_evt1, _x_st4_evt1;
char st5_l, _x_st5_l;
char st3_evt1, _x_st3_evt1;
char mgr_l, _x_mgr_l;
float st5_req_time, _x_st5_req_time;

int main()
{
  st10_evt1 = __VERIFIER_nondet_bool();
  _diverge_delta = __VERIFIER_nondet_float();
  st10_evt0 = __VERIFIER_nondet_bool();
  st10_l = __VERIFIER_nondet_bool();
  st9_evt1 = __VERIFIER_nondet_bool();
  st9_evt0 = __VERIFIER_nondet_bool();
  st9_l = __VERIFIER_nondet_bool();
  st10_req_time = __VERIFIER_nondet_float();
  st8_evt1 = __VERIFIER_nondet_bool();
  st8_evt0 = __VERIFIER_nondet_bool();
  st8_l = __VERIFIER_nondet_bool();
  st9_req_time = __VERIFIER_nondet_float();
  st7_evt1 = __VERIFIER_nondet_bool();
  st7_evt0 = __VERIFIER_nondet_bool();
  st7_l = __VERIFIER_nondet_bool();
  st8_req_time = __VERIFIER_nondet_float();
  st6_evt1 = __VERIFIER_nondet_bool();
  st6_evt0 = __VERIFIER_nondet_bool();
  st6_l = __VERIFIER_nondet_bool();
  st7_req_time = __VERIFIER_nondet_float();
  st5_evt1 = __VERIFIER_nondet_bool();
  st5_evt0 = __VERIFIER_nondet_bool();
  st1_req_time = __VERIFIER_nondet_float();
  st4_evt0 = __VERIFIER_nondet_bool();
  st0_evt0 = __VERIFIER_nondet_bool();
  st0_evt1 = __VERIFIER_nondet_bool();
  mgr_c = __VERIFIER_nondet_float();
  st0_req_time = __VERIFIER_nondet_float();
  st3_evt0 = __VERIFIER_nondet_bool();
  tot_transm_time = __VERIFIER_nondet_float();
  st1_l = __VERIFIER_nondet_bool();
  st3_l = __VERIFIER_nondet_bool();
  delta = __VERIFIER_nondet_float();
  st1_evt0 = __VERIFIER_nondet_bool();
  st0_l = __VERIFIER_nondet_bool();
  st3_req_time = __VERIFIER_nondet_float();
  st1_evt1 = __VERIFIER_nondet_bool();
  mgr_evt0 = __VERIFIER_nondet_bool();
  st2_l = __VERIFIER_nondet_bool();
  mgr_timeout = __VERIFIER_nondet_float();
  st2_req_time = __VERIFIER_nondet_float();
  mgr_evt1 = __VERIFIER_nondet_bool();
  st2_evt0 = __VERIFIER_nondet_bool();
  st4_l = __VERIFIER_nondet_bool();
  st2_evt1 = __VERIFIER_nondet_bool();
  st4_req_time = __VERIFIER_nondet_float();
  st6_req_time = __VERIFIER_nondet_float();
  st4_evt1 = __VERIFIER_nondet_bool();
  st5_l = __VERIFIER_nondet_bool();
  st3_evt1 = __VERIFIER_nondet_bool();
  mgr_l = __VERIFIER_nondet_bool();
  st5_req_time = __VERIFIER_nondet_float();

  int __ok = (((((st10_l != 0) && (((st10_evt1 != 0) && ( !(st10_evt0 != 0))) || ((( !(st10_evt0 != 0)) && ( !(st10_evt1 != 0))) || ((st10_evt0 != 0) && ( !(st10_evt1 != 0)))))) && ( !(st10_req_time <= 0.0))) && ((((st9_l != 0) && (((st9_evt1 != 0) && ( !(st9_evt0 != 0))) || ((( !(st9_evt0 != 0)) && ( !(st9_evt1 != 0))) || ((st9_evt0 != 0) && ( !(st9_evt1 != 0)))))) && ( !(st9_req_time <= 0.0))) && ((((st8_l != 0) && (((st8_evt1 != 0) && ( !(st8_evt0 != 0))) || ((( !(st8_evt0 != 0)) && ( !(st8_evt1 != 0))) || ((st8_evt0 != 0) && ( !(st8_evt1 != 0)))))) && ( !(st8_req_time <= 0.0))) && ((((st7_l != 0) && (((st7_evt1 != 0) && ( !(st7_evt0 != 0))) || ((( !(st7_evt0 != 0)) && ( !(st7_evt1 != 0))) || ((st7_evt0 != 0) && ( !(st7_evt1 != 0)))))) && ( !(st7_req_time <= 0.0))) && ((((st6_l != 0) && (((st6_evt1 != 0) && ( !(st6_evt0 != 0))) || ((( !(st6_evt0 != 0)) && ( !(st6_evt1 != 0))) || ((st6_evt0 != 0) && ( !(st6_evt1 != 0)))))) && ( !(st6_req_time <= 0.0))) && ((((st5_l != 0) && (((st5_evt1 != 0) && ( !(st5_evt0 != 0))) || ((( !(st5_evt0 != 0)) && ( !(st5_evt1 != 0))) || ((st5_evt0 != 0) && ( !(st5_evt1 != 0)))))) && ( !(st5_req_time <= 0.0))) && ((((st4_l != 0) && (((st4_evt1 != 0) && ( !(st4_evt0 != 0))) || ((( !(st4_evt0 != 0)) && ( !(st4_evt1 != 0))) || ((st4_evt0 != 0) && ( !(st4_evt1 != 0)))))) && ( !(st4_req_time <= 0.0))) && ((((st3_l != 0) && (((st3_evt1 != 0) && ( !(st3_evt0 != 0))) || ((( !(st3_evt0 != 0)) && ( !(st3_evt1 != 0))) || ((st3_evt0 != 0) && ( !(st3_evt1 != 0)))))) && ( !(st3_req_time <= 0.0))) && ((((st2_l != 0) && (((st2_evt1 != 0) && ( !(st2_evt0 != 0))) || ((( !(st2_evt0 != 0)) && ( !(st2_evt1 != 0))) || ((st2_evt0 != 0) && ( !(st2_evt1 != 0)))))) && ( !(st2_req_time <= 0.0))) && ((((st1_l != 0) && (((st1_evt1 != 0) && ( !(st1_evt0 != 0))) || ((( !(st1_evt0 != 0)) && ( !(st1_evt1 != 0))) || ((st1_evt0 != 0) && ( !(st1_evt1 != 0)))))) && ( !(st1_req_time <= 0.0))) && ((((st0_l != 0) && (((st0_evt1 != 0) && ( !(st0_evt0 != 0))) || ((( !(st0_evt0 != 0)) && ( !(st0_evt1 != 0))) || ((st0_evt0 != 0) && ( !(st0_evt1 != 0)))))) && ( !(st0_req_time <= 0.0))) && (((((mgr_l != 0) && (((mgr_evt1 != 0) && ( !(mgr_evt0 != 0))) || ((( !(mgr_evt0 != 0)) && ( !(mgr_evt1 != 0))) || ((mgr_evt0 != 0) && ( !(mgr_evt1 != 0)))))) && ((mgr_c == 0.0) && (mgr_timeout == 0.0))) && ((mgr_l != 0) || (mgr_c <= mgr_timeout))) && ((tot_transm_time == 0.0) && (0.0 <= delta)))))))))))))) && (delta == _diverge_delta));
  while (__ok) {
    _x_st10_evt1 = __VERIFIER_nondet_bool();
    _x__diverge_delta = __VERIFIER_nondet_float();
    _x_st10_evt0 = __VERIFIER_nondet_bool();
    _x_st10_l = __VERIFIER_nondet_bool();
    _x_st9_evt1 = __VERIFIER_nondet_bool();
    _x_st9_evt0 = __VERIFIER_nondet_bool();
    _x_st9_l = __VERIFIER_nondet_bool();
    _x_st10_req_time = __VERIFIER_nondet_float();
    _x_st8_evt1 = __VERIFIER_nondet_bool();
    _x_st8_evt0 = __VERIFIER_nondet_bool();
    _x_st8_l = __VERIFIER_nondet_bool();
    _x_st9_req_time = __VERIFIER_nondet_float();
    _x_st7_evt1 = __VERIFIER_nondet_bool();
    _x_st7_evt0 = __VERIFIER_nondet_bool();
    _x_st7_l = __VERIFIER_nondet_bool();
    _x_st8_req_time = __VERIFIER_nondet_float();
    _x_st6_evt1 = __VERIFIER_nondet_bool();
    _x_st6_evt0 = __VERIFIER_nondet_bool();
    _x_st6_l = __VERIFIER_nondet_bool();
    _x_st7_req_time = __VERIFIER_nondet_float();
    _x_st5_evt1 = __VERIFIER_nondet_bool();
    _x_st5_evt0 = __VERIFIER_nondet_bool();
    _x_st1_req_time = __VERIFIER_nondet_float();
    _x_st4_evt0 = __VERIFIER_nondet_bool();
    _x_st0_evt0 = __VERIFIER_nondet_bool();
    _x_st0_evt1 = __VERIFIER_nondet_bool();
    _x_mgr_c = __VERIFIER_nondet_float();
    _x_st0_req_time = __VERIFIER_nondet_float();
    _x_st3_evt0 = __VERIFIER_nondet_bool();
    _x_tot_transm_time = __VERIFIER_nondet_float();
    _x_st1_l = __VERIFIER_nondet_bool();
    _x_st3_l = __VERIFIER_nondet_bool();
    _x_delta = __VERIFIER_nondet_float();
    _x_st1_evt0 = __VERIFIER_nondet_bool();
    _x_st0_l = __VERIFIER_nondet_bool();
    _x_st3_req_time = __VERIFIER_nondet_float();
    _x_st1_evt1 = __VERIFIER_nondet_bool();
    _x_mgr_evt0 = __VERIFIER_nondet_bool();
    _x_st2_l = __VERIFIER_nondet_bool();
    _x_mgr_timeout = __VERIFIER_nondet_float();
    _x_st2_req_time = __VERIFIER_nondet_float();
    _x_mgr_evt1 = __VERIFIER_nondet_bool();
    _x_st2_evt0 = __VERIFIER_nondet_bool();
    _x_st4_l = __VERIFIER_nondet_bool();
    _x_st2_evt1 = __VERIFIER_nondet_bool();
    _x_st4_req_time = __VERIFIER_nondet_float();
    _x_st6_req_time = __VERIFIER_nondet_float();
    _x_st4_evt1 = __VERIFIER_nondet_bool();
    _x_st5_l = __VERIFIER_nondet_bool();
    _x_st3_evt1 = __VERIFIER_nondet_bool();
    _x_mgr_l = __VERIFIER_nondet_bool();
    _x_st5_req_time = __VERIFIER_nondet_float();

    __ok = (((((((((_x_st10_evt1 != 0) && ( !(_x_st10_evt0 != 0))) || ((( !(_x_st10_evt0 != 0)) && ( !(_x_st10_evt1 != 0))) || ((_x_st10_evt0 != 0) && ( !(_x_st10_evt1 != 0))))) && ( !(_x_st10_req_time <= 0.0))) && ((((st10_l != 0) == (_x_st10_l != 0)) && (st10_req_time == _x_st10_req_time)) || ( !(( !(delta <= 0.0)) || ((st10_evt1 != 0) && ( !(st10_evt0 != 0))))))) && ((((( !(st10_evt0 != 0)) && ( !(st10_evt1 != 0))) && ( !(_x_st10_l != 0))) && ((st10_req_time == _x_st10_req_time) && (_x_mgr_timeout == st10_req_time))) || ( !((st10_l != 0) && ((delta == 0.0) && ((( !(st10_evt0 != 0)) && ( !(st10_evt1 != 0))) || ((st10_evt0 != 0) && ( !(st10_evt1 != 0))))))))) && ((((st10_evt0 != 0) && ( !(st10_evt1 != 0))) && (( !(mgr_c <= 0.0)) && (_x_st10_l != 0))) || ( !(( !(st10_l != 0)) && ((delta == 0.0) && ((( !(st10_evt0 != 0)) && ( !(st10_evt1 != 0))) || ((st10_evt0 != 0) && ( !(st10_evt1 != 0))))))))) && ((((((((_x_st9_evt1 != 0) && ( !(_x_st9_evt0 != 0))) || ((( !(_x_st9_evt0 != 0)) && ( !(_x_st9_evt1 != 0))) || ((_x_st9_evt0 != 0) && ( !(_x_st9_evt1 != 0))))) && ( !(_x_st9_req_time <= 0.0))) && ((((st9_l != 0) == (_x_st9_l != 0)) && (st9_req_time == _x_st9_req_time)) || ( !(( !(delta <= 0.0)) || ((st9_evt1 != 0) && ( !(st9_evt0 != 0))))))) && ((((( !(st9_evt0 != 0)) && ( !(st9_evt1 != 0))) && ( !(_x_st9_l != 0))) && ((st9_req_time == _x_st9_req_time) && (_x_mgr_timeout == st9_req_time))) || ( !((st9_l != 0) && ((delta == 0.0) && ((( !(st9_evt0 != 0)) && ( !(st9_evt1 != 0))) || ((st9_evt0 != 0) && ( !(st9_evt1 != 0))))))))) && ((((st9_evt0 != 0) && ( !(st9_evt1 != 0))) && (( !(mgr_c <= 0.0)) && (_x_st9_l != 0))) || ( !(( !(st9_l != 0)) && ((delta == 0.0) && ((( !(st9_evt0 != 0)) && ( !(st9_evt1 != 0))) || ((st9_evt0 != 0) && ( !(st9_evt1 != 0))))))))) && ((((((((_x_st8_evt1 != 0) && ( !(_x_st8_evt0 != 0))) || ((( !(_x_st8_evt0 != 0)) && ( !(_x_st8_evt1 != 0))) || ((_x_st8_evt0 != 0) && ( !(_x_st8_evt1 != 0))))) && ( !(_x_st8_req_time <= 0.0))) && ((((st8_l != 0) == (_x_st8_l != 0)) && (st8_req_time == _x_st8_req_time)) || ( !(( !(delta <= 0.0)) || ((st8_evt1 != 0) && ( !(st8_evt0 != 0))))))) && ((((( !(st8_evt0 != 0)) && ( !(st8_evt1 != 0))) && ( !(_x_st8_l != 0))) && ((st8_req_time == _x_st8_req_time) && (_x_mgr_timeout == st8_req_time))) || ( !((st8_l != 0) && ((delta == 0.0) && ((( !(st8_evt0 != 0)) && ( !(st8_evt1 != 0))) || ((st8_evt0 != 0) && ( !(st8_evt1 != 0))))))))) && ((((st8_evt0 != 0) && ( !(st8_evt1 != 0))) && (( !(mgr_c <= 0.0)) && (_x_st8_l != 0))) || ( !(( !(st8_l != 0)) && ((delta == 0.0) && ((( !(st8_evt0 != 0)) && ( !(st8_evt1 != 0))) || ((st8_evt0 != 0) && ( !(st8_evt1 != 0))))))))) && ((((((((_x_st7_evt1 != 0) && ( !(_x_st7_evt0 != 0))) || ((( !(_x_st7_evt0 != 0)) && ( !(_x_st7_evt1 != 0))) || ((_x_st7_evt0 != 0) && ( !(_x_st7_evt1 != 0))))) && ( !(_x_st7_req_time <= 0.0))) && ((((st7_l != 0) == (_x_st7_l != 0)) && (st7_req_time == _x_st7_req_time)) || ( !(( !(delta <= 0.0)) || ((st7_evt1 != 0) && ( !(st7_evt0 != 0))))))) && ((((( !(st7_evt0 != 0)) && ( !(st7_evt1 != 0))) && ( !(_x_st7_l != 0))) && ((st7_req_time == _x_st7_req_time) && (_x_mgr_timeout == st7_req_time))) || ( !((st7_l != 0) && ((delta == 0.0) && ((( !(st7_evt0 != 0)) && ( !(st7_evt1 != 0))) || ((st7_evt0 != 0) && ( !(st7_evt1 != 0))))))))) && ((((st7_evt0 != 0) && ( !(st7_evt1 != 0))) && (( !(mgr_c <= 0.0)) && (_x_st7_l != 0))) || ( !(( !(st7_l != 0)) && ((delta == 0.0) && ((( !(st7_evt0 != 0)) && ( !(st7_evt1 != 0))) || ((st7_evt0 != 0) && ( !(st7_evt1 != 0))))))))) && ((((((((_x_st6_evt1 != 0) && ( !(_x_st6_evt0 != 0))) || ((( !(_x_st6_evt0 != 0)) && ( !(_x_st6_evt1 != 0))) || ((_x_st6_evt0 != 0) && ( !(_x_st6_evt1 != 0))))) && ( !(_x_st6_req_time <= 0.0))) && ((((st6_l != 0) == (_x_st6_l != 0)) && (st6_req_time == _x_st6_req_time)) || ( !(( !(delta <= 0.0)) || ((st6_evt1 != 0) && ( !(st6_evt0 != 0))))))) && ((((( !(st6_evt0 != 0)) && ( !(st6_evt1 != 0))) && ( !(_x_st6_l != 0))) && ((st6_req_time == _x_st6_req_time) && (_x_mgr_timeout == st6_req_time))) || ( !((st6_l != 0) && ((delta == 0.0) && ((( !(st6_evt0 != 0)) && ( !(st6_evt1 != 0))) || ((st6_evt0 != 0) && ( !(st6_evt1 != 0))))))))) && ((((st6_evt0 != 0) && ( !(st6_evt1 != 0))) && (( !(mgr_c <= 0.0)) && (_x_st6_l != 0))) || ( !(( !(st6_l != 0)) && ((delta == 0.0) && ((( !(st6_evt0 != 0)) && ( !(st6_evt1 != 0))) || ((st6_evt0 != 0) && ( !(st6_evt1 != 0))))))))) && ((((((((_x_st5_evt1 != 0) && ( !(_x_st5_evt0 != 0))) || ((( !(_x_st5_evt0 != 0)) && ( !(_x_st5_evt1 != 0))) || ((_x_st5_evt0 != 0) && ( !(_x_st5_evt1 != 0))))) && ( !(_x_st5_req_time <= 0.0))) && ((((st5_l != 0) == (_x_st5_l != 0)) && (st5_req_time == _x_st5_req_time)) || ( !(( !(delta <= 0.0)) || ((st5_evt1 != 0) && ( !(st5_evt0 != 0))))))) && ((((( !(st5_evt0 != 0)) && ( !(st5_evt1 != 0))) && ( !(_x_st5_l != 0))) && ((st5_req_time == _x_st5_req_time) && (_x_mgr_timeout == st5_req_time))) || ( !((st5_l != 0) && ((delta == 0.0) && ((( !(st5_evt0 != 0)) && ( !(st5_evt1 != 0))) || ((st5_evt0 != 0) && ( !(st5_evt1 != 0))))))))) && ((((st5_evt0 != 0) && ( !(st5_evt1 != 0))) && (( !(mgr_c <= 0.0)) && (_x_st5_l != 0))) || ( !(( !(st5_l != 0)) && ((delta == 0.0) && ((( !(st5_evt0 != 0)) && ( !(st5_evt1 != 0))) || ((st5_evt0 != 0) && ( !(st5_evt1 != 0))))))))) && ((((((((_x_st4_evt1 != 0) && ( !(_x_st4_evt0 != 0))) || ((( !(_x_st4_evt0 != 0)) && ( !(_x_st4_evt1 != 0))) || ((_x_st4_evt0 != 0) && ( !(_x_st4_evt1 != 0))))) && ( !(_x_st4_req_time <= 0.0))) && ((((st4_l != 0) == (_x_st4_l != 0)) && (st4_req_time == _x_st4_req_time)) || ( !(( !(delta <= 0.0)) || ((st4_evt1 != 0) && ( !(st4_evt0 != 0))))))) && ((((( !(st4_evt0 != 0)) && ( !(st4_evt1 != 0))) && ( !(_x_st4_l != 0))) && ((st4_req_time == _x_st4_req_time) && (_x_mgr_timeout == st4_req_time))) || ( !((st4_l != 0) && ((delta == 0.0) && ((( !(st4_evt0 != 0)) && ( !(st4_evt1 != 0))) || ((st4_evt0 != 0) && ( !(st4_evt1 != 0))))))))) && ((((st4_evt0 != 0) && ( !(st4_evt1 != 0))) && (( !(mgr_c <= 0.0)) && (_x_st4_l != 0))) || ( !(( !(st4_l != 0)) && ((delta == 0.0) && ((( !(st4_evt0 != 0)) && ( !(st4_evt1 != 0))) || ((st4_evt0 != 0) && ( !(st4_evt1 != 0))))))))) && ((((((((_x_st3_evt1 != 0) && ( !(_x_st3_evt0 != 0))) || ((( !(_x_st3_evt0 != 0)) && ( !(_x_st3_evt1 != 0))) || ((_x_st3_evt0 != 0) && ( !(_x_st3_evt1 != 0))))) && ( !(_x_st3_req_time <= 0.0))) && ((((st3_l != 0) == (_x_st3_l != 0)) && (st3_req_time == _x_st3_req_time)) || ( !(( !(delta <= 0.0)) || ((st3_evt1 != 0) && ( !(st3_evt0 != 0))))))) && ((((( !(st3_evt0 != 0)) && ( !(st3_evt1 != 0))) && ( !(_x_st3_l != 0))) && ((st3_req_time == _x_st3_req_time) && (_x_mgr_timeout == st3_req_time))) || ( !((st3_l != 0) && ((delta == 0.0) && ((( !(st3_evt0 != 0)) && ( !(st3_evt1 != 0))) || ((st3_evt0 != 0) && ( !(st3_evt1 != 0))))))))) && ((((st3_evt0 != 0) && ( !(st3_evt1 != 0))) && (( !(mgr_c <= 0.0)) && (_x_st3_l != 0))) || ( !(( !(st3_l != 0)) && ((delta == 0.0) && ((( !(st3_evt0 != 0)) && ( !(st3_evt1 != 0))) || ((st3_evt0 != 0) && ( !(st3_evt1 != 0))))))))) && ((((((((_x_st2_evt1 != 0) && ( !(_x_st2_evt0 != 0))) || ((( !(_x_st2_evt0 != 0)) && ( !(_x_st2_evt1 != 0))) || ((_x_st2_evt0 != 0) && ( !(_x_st2_evt1 != 0))))) && ( !(_x_st2_req_time <= 0.0))) && ((((st2_l != 0) == (_x_st2_l != 0)) && (st2_req_time == _x_st2_req_time)) || ( !(( !(delta <= 0.0)) || ((st2_evt1 != 0) && ( !(st2_evt0 != 0))))))) && ((((( !(st2_evt0 != 0)) && ( !(st2_evt1 != 0))) && ( !(_x_st2_l != 0))) && ((st2_req_time == _x_st2_req_time) && (_x_mgr_timeout == st2_req_time))) || ( !((st2_l != 0) && ((delta == 0.0) && ((( !(st2_evt0 != 0)) && ( !(st2_evt1 != 0))) || ((st2_evt0 != 0) && ( !(st2_evt1 != 0))))))))) && ((((st2_evt0 != 0) && ( !(st2_evt1 != 0))) && (( !(mgr_c <= 0.0)) && (_x_st2_l != 0))) || ( !(( !(st2_l != 0)) && ((delta == 0.0) && ((( !(st2_evt0 != 0)) && ( !(st2_evt1 != 0))) || ((st2_evt0 != 0) && ( !(st2_evt1 != 0))))))))) && ((((((((_x_st1_evt1 != 0) && ( !(_x_st1_evt0 != 0))) || ((( !(_x_st1_evt0 != 0)) && ( !(_x_st1_evt1 != 0))) || ((_x_st1_evt0 != 0) && ( !(_x_st1_evt1 != 0))))) && ( !(_x_st1_req_time <= 0.0))) && ((((st1_l != 0) == (_x_st1_l != 0)) && (st1_req_time == _x_st1_req_time)) || ( !(( !(delta <= 0.0)) || ((st1_evt1 != 0) && ( !(st1_evt0 != 0))))))) && ((((( !(st1_evt0 != 0)) && ( !(st1_evt1 != 0))) && ( !(_x_st1_l != 0))) && ((st1_req_time == _x_st1_req_time) && (_x_mgr_timeout == st1_req_time))) || ( !((st1_l != 0) && ((delta == 0.0) && ((( !(st1_evt0 != 0)) && ( !(st1_evt1 != 0))) || ((st1_evt0 != 0) && ( !(st1_evt1 != 0))))))))) && ((((st1_evt0 != 0) && ( !(st1_evt1 != 0))) && (( !(mgr_c <= 0.0)) && (_x_st1_l != 0))) || ( !(( !(st1_l != 0)) && ((delta == 0.0) && ((( !(st1_evt0 != 0)) && ( !(st1_evt1 != 0))) || ((st1_evt0 != 0) && ( !(st1_evt1 != 0))))))))) && ((((((((_x_st0_evt1 != 0) && ( !(_x_st0_evt0 != 0))) || ((( !(_x_st0_evt0 != 0)) && ( !(_x_st0_evt1 != 0))) || ((_x_st0_evt0 != 0) && ( !(_x_st0_evt1 != 0))))) && ( !(_x_st0_req_time <= 0.0))) && ((((st0_l != 0) == (_x_st0_l != 0)) && (st0_req_time == _x_st0_req_time)) || ( !(( !(delta <= 0.0)) || ((st0_evt1 != 0) && ( !(st0_evt0 != 0))))))) && ((((( !(st0_evt0 != 0)) && ( !(st0_evt1 != 0))) && ( !(_x_st0_l != 0))) && ((st0_req_time == _x_st0_req_time) && (_x_mgr_timeout == st0_req_time))) || ( !((st0_l != 0) && ((delta == 0.0) && ((( !(st0_evt0 != 0)) && ( !(st0_evt1 != 0))) || ((st0_evt0 != 0) && ( !(st0_evt1 != 0))))))))) && ((((st0_evt0 != 0) && ( !(st0_evt1 != 0))) && ((_x_st0_l != 0) && ( !(mgr_c <= 0.0)))) || ( !(( !(st0_l != 0)) && ((delta == 0.0) && ((( !(st0_evt0 != 0)) && ( !(st0_evt1 != 0))) || ((st0_evt0 != 0) && ( !(st0_evt1 != 0))))))))) && ((((((((_x_mgr_evt1 != 0) && ( !(_x_mgr_evt0 != 0))) || ((( !(_x_mgr_evt0 != 0)) && ( !(_x_mgr_evt1 != 0))) || ((_x_mgr_evt0 != 0) && ( !(_x_mgr_evt1 != 0))))) && ((_x_mgr_l != 0) || (_x_mgr_c <= _x_mgr_timeout))) && (((((mgr_l != 0) == (_x_mgr_l != 0)) && ((delta + (mgr_c + (-1.0 * _x_mgr_c))) == 0.0)) && (mgr_timeout == _x_mgr_timeout)) || ( !(((mgr_evt1 != 0) && ( !(mgr_evt0 != 0))) || ( !(delta <= 0.0)))))) && (((( !(mgr_evt0 != 0)) && ( !(mgr_evt1 != 0))) && (( !(_x_mgr_l != 0)) && (_x_mgr_c == 0.0))) || ( !((mgr_l != 0) && (((( !(mgr_evt0 != 0)) && ( !(mgr_evt1 != 0))) || ((mgr_evt0 != 0) && ( !(mgr_evt1 != 0)))) && (delta == 0.0)))))) && ((((_x_mgr_l != 0) && ((mgr_evt0 != 0) && ( !(mgr_evt1 != 0)))) && ((_x_mgr_c == 0.0) && (_x_mgr_timeout == 0.0))) || ( !(( !(mgr_l != 0)) && (((( !(mgr_evt0 != 0)) && ( !(mgr_evt1 != 0))) || ((mgr_evt0 != 0) && ( !(mgr_evt1 != 0)))) && (delta == 0.0)))))) && ((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((0.0 <= _x_delta) && (((st0_evt1 != 0) && ( !(st0_evt0 != 0))) || ((st1_evt1 != 0) && ( !(st1_evt0 != 0))))) && (((st0_evt1 != 0) && ( !(st0_evt0 != 0))) || ((st2_evt1 != 0) && ( !(st2_evt0 != 0))))) && (((st0_evt1 != 0) && ( !(st0_evt0 != 0))) || ((st3_evt1 != 0) && ( !(st3_evt0 != 0))))) && (((st0_evt1 != 0) && ( !(st0_evt0 != 0))) || ((st4_evt1 != 0) && ( !(st4_evt0 != 0))))) && (((st0_evt1 != 0) && ( !(st0_evt0 != 0))) || ((st5_evt1 != 0) && ( !(st5_evt0 != 0))))) && (((st0_evt1 != 0) && ( !(st0_evt0 != 0))) || ((st6_evt1 != 0) && ( !(st6_evt0 != 0))))) && (((st0_evt1 != 0) && ( !(st0_evt0 != 0))) || ((st7_evt1 != 0) && ( !(st7_evt0 != 0))))) && (((st0_evt1 != 0) && ( !(st0_evt0 != 0))) || ((st8_evt1 != 0) && ( !(st8_evt0 != 0))))) && (((st0_evt1 != 0) && ( !(st0_evt0 != 0))) || ((st9_evt1 != 0) && ( !(st9_evt0 != 0))))) && (((st0_evt1 != 0) && ( !(st0_evt0 != 0))) || ((st10_evt1 != 0) && ( !(st10_evt0 != 0))))) && (((st1_evt1 != 0) && ( !(st1_evt0 != 0))) || ((st2_evt1 != 0) && ( !(st2_evt0 != 0))))) && (((st1_evt1 != 0) && ( !(st1_evt0 != 0))) || ((st3_evt1 != 0) && ( !(st3_evt0 != 0))))) && (((st1_evt1 != 0) && ( !(st1_evt0 != 0))) || ((st4_evt1 != 0) && ( !(st4_evt0 != 0))))) && (((st1_evt1 != 0) && ( !(st1_evt0 != 0))) || ((st5_evt1 != 0) && ( !(st5_evt0 != 0))))) && (((st1_evt1 != 0) && ( !(st1_evt0 != 0))) || ((st6_evt1 != 0) && ( !(st6_evt0 != 0))))) && (((st1_evt1 != 0) && ( !(st1_evt0 != 0))) || ((st7_evt1 != 0) && ( !(st7_evt0 != 0))))) && (((st1_evt1 != 0) && ( !(st1_evt0 != 0))) || ((st8_evt1 != 0) && ( !(st8_evt0 != 0))))) && (((st1_evt1 != 0) && ( !(st1_evt0 != 0))) || ((st9_evt1 != 0) && ( !(st9_evt0 != 0))))) && (((st1_evt1 != 0) && ( !(st1_evt0 != 0))) || ((st10_evt1 != 0) && ( !(st10_evt0 != 0))))) && (((st2_evt1 != 0) && ( !(st2_evt0 != 0))) || ((st3_evt1 != 0) && ( !(st3_evt0 != 0))))) && (((st2_evt1 != 0) && ( !(st2_evt0 != 0))) || ((st4_evt1 != 0) && ( !(st4_evt0 != 0))))) && (((st2_evt1 != 0) && ( !(st2_evt0 != 0))) || ((st5_evt1 != 0) && ( !(st5_evt0 != 0))))) && (((st2_evt1 != 0) && ( !(st2_evt0 != 0))) || ((st6_evt1 != 0) && ( !(st6_evt0 != 0))))) && (((st2_evt1 != 0) && ( !(st2_evt0 != 0))) || ((st7_evt1 != 0) && ( !(st7_evt0 != 0))))) && (((st2_evt1 != 0) && ( !(st2_evt0 != 0))) || ((st8_evt1 != 0) && ( !(st8_evt0 != 0))))) && (((st2_evt1 != 0) && ( !(st2_evt0 != 0))) || ((st9_evt1 != 0) && ( !(st9_evt0 != 0))))) && (((st2_evt1 != 0) && ( !(st2_evt0 != 0))) || ((st10_evt1 != 0) && ( !(st10_evt0 != 0))))) && (((st3_evt1 != 0) && ( !(st3_evt0 != 0))) || ((st4_evt1 != 0) && ( !(st4_evt0 != 0))))) && (((st3_evt1 != 0) && ( !(st3_evt0 != 0))) || ((st5_evt1 != 0) && ( !(st5_evt0 != 0))))) && (((st3_evt1 != 0) && ( !(st3_evt0 != 0))) || ((st6_evt1 != 0) && ( !(st6_evt0 != 0))))) && (((st3_evt1 != 0) && ( !(st3_evt0 != 0))) || ((st7_evt1 != 0) && ( !(st7_evt0 != 0))))) && (((st3_evt1 != 0) && ( !(st3_evt0 != 0))) || ((st8_evt1 != 0) && ( !(st8_evt0 != 0))))) && (((st3_evt1 != 0) && ( !(st3_evt0 != 0))) || ((st9_evt1 != 0) && ( !(st9_evt0 != 0))))) && (((st3_evt1 != 0) && ( !(st3_evt0 != 0))) || ((st10_evt1 != 0) && ( !(st10_evt0 != 0))))) && (((st4_evt1 != 0) && ( !(st4_evt0 != 0))) || ((st5_evt1 != 0) && ( !(st5_evt0 != 0))))) && (((st4_evt1 != 0) && ( !(st4_evt0 != 0))) || ((st6_evt1 != 0) && ( !(st6_evt0 != 0))))) && (((st4_evt1 != 0) && ( !(st4_evt0 != 0))) || ((st7_evt1 != 0) && ( !(st7_evt0 != 0))))) && (((st4_evt1 != 0) && ( !(st4_evt0 != 0))) || ((st8_evt1 != 0) && ( !(st8_evt0 != 0))))) && (((st4_evt1 != 0) && ( !(st4_evt0 != 0))) || ((st9_evt1 != 0) && ( !(st9_evt0 != 0))))) && (((st4_evt1 != 0) && ( !(st4_evt0 != 0))) || ((st10_evt1 != 0) && ( !(st10_evt0 != 0))))) && (((st5_evt1 != 0) && ( !(st5_evt0 != 0))) || ((st6_evt1 != 0) && ( !(st6_evt0 != 0))))) && (((st5_evt1 != 0) && ( !(st5_evt0 != 0))) || ((st7_evt1 != 0) && ( !(st7_evt0 != 0))))) && (((st5_evt1 != 0) && ( !(st5_evt0 != 0))) || ((st8_evt1 != 0) && ( !(st8_evt0 != 0))))) && (((st5_evt1 != 0) && ( !(st5_evt0 != 0))) || ((st9_evt1 != 0) && ( !(st9_evt0 != 0))))) && (((st5_evt1 != 0) && ( !(st5_evt0 != 0))) || ((st10_evt1 != 0) && ( !(st10_evt0 != 0))))) && (((st6_evt1 != 0) && ( !(st6_evt0 != 0))) || ((st7_evt1 != 0) && ( !(st7_evt0 != 0))))) && (((st6_evt1 != 0) && ( !(st6_evt0 != 0))) || ((st8_evt1 != 0) && ( !(st8_evt0 != 0))))) && (((st6_evt1 != 0) && ( !(st6_evt0 != 0))) || ((st9_evt1 != 0) && ( !(st9_evt0 != 0))))) && (((st6_evt1 != 0) && ( !(st6_evt0 != 0))) || ((st10_evt1 != 0) && ( !(st10_evt0 != 0))))) && (((st7_evt1 != 0) && ( !(st7_evt0 != 0))) || ((st8_evt1 != 0) && ( !(st8_evt0 != 0))))) && (((st7_evt1 != 0) && ( !(st7_evt0 != 0))) || ((st9_evt1 != 0) && ( !(st9_evt0 != 0))))) && (((st7_evt1 != 0) && ( !(st7_evt0 != 0))) || ((st10_evt1 != 0) && ( !(st10_evt0 != 0))))) && (((st8_evt1 != 0) && ( !(st8_evt0 != 0))) || ((st9_evt1 != 0) && ( !(st9_evt0 != 0))))) && (((st8_evt1 != 0) && ( !(st8_evt0 != 0))) || ((st10_evt1 != 0) && ( !(st10_evt0 != 0))))) && (((st9_evt1 != 0) && ( !(st9_evt0 != 0))) || ((st10_evt1 != 0) && ( !(st10_evt0 != 0))))) && ((( !(mgr_evt0 != 0)) && ( !(mgr_evt1 != 0))) == ((( !(st10_evt0 != 0)) && ( !(st10_evt1 != 0))) || ((( !(st9_evt0 != 0)) && ( !(st9_evt1 != 0))) || ((( !(st8_evt0 != 0)) && ( !(st8_evt1 != 0))) || ((( !(st7_evt0 != 0)) && ( !(st7_evt1 != 0))) || ((( !(st6_evt0 != 0)) && ( !(st6_evt1 != 0))) || ((( !(st5_evt0 != 0)) && ( !(st5_evt1 != 0))) || ((( !(st4_evt0 != 0)) && ( !(st4_evt1 != 0))) || ((( !(st3_evt0 != 0)) && ( !(st3_evt1 != 0))) || ((( !(st2_evt0 != 0)) && ( !(st2_evt1 != 0))) || ((( !(st0_evt0 != 0)) && ( !(st0_evt1 != 0))) || (( !(st1_evt0 != 0)) && ( !(st1_evt1 != 0))))))))))))))) && (((mgr_evt0 != 0) && ( !(mgr_evt1 != 0))) == (((st10_evt0 != 0) && ( !(st10_evt1 != 0))) || (((st9_evt0 != 0) && ( !(st9_evt1 != 0))) || (((st8_evt0 != 0) && ( !(st8_evt1 != 0))) || (((st7_evt0 != 0) && ( !(st7_evt1 != 0))) || (((st6_evt0 != 0) && ( !(st6_evt1 != 0))) || (((st5_evt0 != 0) && ( !(st5_evt1 != 0))) || (((st4_evt0 != 0) && ( !(st4_evt1 != 0))) || (((st3_evt0 != 0) && ( !(st3_evt1 != 0))) || (((st2_evt0 != 0) && ( !(st2_evt1 != 0))) || (((st0_evt0 != 0) && ( !(st0_evt1 != 0))) || ((st1_evt0 != 0) && ( !(st1_evt1 != 0))))))))))))))) && (((tot_transm_time + ((-1.0 * _x_tot_transm_time) + mgr_c)) == 0.0) || ( !((_x_mgr_l != 0) && ( !(mgr_l != 0)))))) && (((_x_mgr_l != 0) && ( !(mgr_l != 0))) || (tot_transm_time == _x_tot_transm_time))))))))))))))) && (((delta == _x__diverge_delta) || ( !(1.0 <= _diverge_delta))) && ((1.0 <= _diverge_delta) || ((delta + (_diverge_delta + (-1.0 * _x__diverge_delta))) == 0.0))));
    st10_evt1 = _x_st10_evt1;
    _diverge_delta = _x__diverge_delta;
    st10_evt0 = _x_st10_evt0;
    st10_l = _x_st10_l;
    st9_evt1 = _x_st9_evt1;
    st9_evt0 = _x_st9_evt0;
    st9_l = _x_st9_l;
    st10_req_time = _x_st10_req_time;
    st8_evt1 = _x_st8_evt1;
    st8_evt0 = _x_st8_evt0;
    st8_l = _x_st8_l;
    st9_req_time = _x_st9_req_time;
    st7_evt1 = _x_st7_evt1;
    st7_evt0 = _x_st7_evt0;
    st7_l = _x_st7_l;
    st8_req_time = _x_st8_req_time;
    st6_evt1 = _x_st6_evt1;
    st6_evt0 = _x_st6_evt0;
    st6_l = _x_st6_l;
    st7_req_time = _x_st7_req_time;
    st5_evt1 = _x_st5_evt1;
    st5_evt0 = _x_st5_evt0;
    st1_req_time = _x_st1_req_time;
    st4_evt0 = _x_st4_evt0;
    st0_evt0 = _x_st0_evt0;
    st0_evt1 = _x_st0_evt1;
    mgr_c = _x_mgr_c;
    st0_req_time = _x_st0_req_time;
    st3_evt0 = _x_st3_evt0;
    tot_transm_time = _x_tot_transm_time;
    st1_l = _x_st1_l;
    st3_l = _x_st3_l;
    delta = _x_delta;
    st1_evt0 = _x_st1_evt0;
    st0_l = _x_st0_l;
    st3_req_time = _x_st3_req_time;
    st1_evt1 = _x_st1_evt1;
    mgr_evt0 = _x_mgr_evt0;
    st2_l = _x_st2_l;
    mgr_timeout = _x_mgr_timeout;
    st2_req_time = _x_st2_req_time;
    mgr_evt1 = _x_mgr_evt1;
    st2_evt0 = _x_st2_evt0;
    st4_l = _x_st4_l;
    st2_evt1 = _x_st2_evt1;
    st4_req_time = _x_st4_req_time;
    st6_req_time = _x_st6_req_time;
    st4_evt1 = _x_st4_evt1;
    st5_l = _x_st5_l;
    st3_evt1 = _x_st3_evt1;
    mgr_l = _x_mgr_l;
    st5_req_time = _x_st5_req_time;

  }
}
