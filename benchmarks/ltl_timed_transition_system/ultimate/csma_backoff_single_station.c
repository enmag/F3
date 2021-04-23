//@ ltl invariant negative: ( ( ([] (<> ( (! AP((st_l0 != 0))) && (! AP((st_l1 != 0)))))) || (! ([] (<> ( AP((st_l1 != 0)) && (! AP((st_l0 != 0)))))))) || (! ([] (<> AP((1.0 <= _diverge_delta))))));

extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);

char __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}


float _diverge_delta, _x__diverge_delta;
char env_evt2, _x_env_evt2;
char env_evt1, _x_env_evt1;
char env_evt0, _x_env_evt0;
char st_l1, _x_st_l1;
char st_l0, _x_st_l0;
float delta, _x_delta;
char bus_evt0, _x_bus_evt0;
char bus_evt1, _x_bus_evt1;
float st_x, _x_st_x;
char bus_l0, _x_bus_l0;
char bus_evt2, _x_bus_evt2;
char bus_cd_id, _x_bus_cd_id;
char st_evt0, _x_st_evt0;
char bus_l1, _x_bus_l1;
float st_backoff, _x_st_backoff;
float bus_x, _x_bus_x;
char st_evt1, _x_st_evt1;
char st_evt2, _x_st_evt2;

int main()
{
  _diverge_delta = __VERIFIER_nondet_float();
  env_evt2 = __VERIFIER_nondet_bool();
  env_evt1 = __VERIFIER_nondet_bool();
  env_evt0 = __VERIFIER_nondet_bool();
  st_l1 = __VERIFIER_nondet_bool();
  st_l0 = __VERIFIER_nondet_bool();
  delta = __VERIFIER_nondet_float();
  bus_evt0 = __VERIFIER_nondet_bool();
  bus_evt1 = __VERIFIER_nondet_bool();
  st_x = __VERIFIER_nondet_float();
  bus_l0 = __VERIFIER_nondet_bool();
  bus_evt2 = __VERIFIER_nondet_bool();
  bus_cd_id = __VERIFIER_nondet_bool();
  st_evt0 = __VERIFIER_nondet_bool();
  bus_l1 = __VERIFIER_nondet_bool();
  st_backoff = __VERIFIER_nondet_float();
  bus_x = __VERIFIER_nondet_float();
  st_evt1 = __VERIFIER_nondet_bool();
  st_evt2 = __VERIFIER_nondet_bool();

  int __ok = ((((( !(env_evt2 != 0)) && ((env_evt0 != 0) && ( !(env_evt1 != 0)))) || (((( !(env_evt2 != 0)) && (( !(env_evt0 != 0)) && ( !(env_evt1 != 0)))) || ((env_evt2 != 0) && (( !(env_evt0 != 0)) && ( !(env_evt1 != 0))))) || ((( !(env_evt2 != 0)) && ((env_evt1 != 0) && ( !(env_evt0 != 0)))) || ((env_evt2 != 0) && ((env_evt1 != 0) && ( !(env_evt0 != 0))))))) && (((((((( !(st_l0 != 0)) && ( !(st_l1 != 0))) && (st_x == 0.0)) && (13.0 <= st_backoff)) && ((( !(st_evt2 != 0)) && ((st_evt0 != 0) && ( !(st_evt1 != 0)))) || (((( !(st_evt2 != 0)) && (( !(st_evt0 != 0)) && ( !(st_evt1 != 0)))) || ((st_evt2 != 0) && (( !(st_evt0 != 0)) && ( !(st_evt1 != 0))))) || ((( !(st_evt2 != 0)) && ((st_evt1 != 0) && ( !(st_evt0 != 0)))) || ((st_evt2 != 0) && ((st_evt1 != 0) && ( !(st_evt0 != 0)))))))) && ((( !(st_l0 != 0)) && ( !(st_l1 != 0))) || (((st_l1 != 0) && ( !(st_l0 != 0))) || ((st_l0 != 0) && ( !(st_l1 != 0)))))) && ((st_x <= 404.0) || ( !((st_l1 != 0) && ( !(st_l0 != 0)))))) && ((((((( !(bus_l0 != 0)) && ( !(bus_l1 != 0))) && ((bus_cd_id != 0) && (bus_x == 0.0))) && ((( !(bus_evt2 != 0)) && (( !(bus_evt0 != 0)) && ( !(bus_evt1 != 0)))) || ((((bus_evt2 != 0) && (( !(bus_evt0 != 0)) && ( !(bus_evt1 != 0)))) || (( !(bus_evt2 != 0)) && ((bus_evt1 != 0) && ( !(bus_evt0 != 0))))) || (((bus_evt2 != 0) && ((bus_evt1 != 0) && ( !(bus_evt0 != 0)))) || (( !(bus_evt2 != 0)) && ((bus_evt0 != 0) && ( !(bus_evt1 != 0)))))))) && (((( !(bus_l0 != 0)) && ( !(bus_l1 != 0))) || ((bus_l1 != 0) && ( !(bus_l0 != 0)))) || (((bus_l0 != 0) && ( !(bus_l1 != 0))) || ((bus_l0 != 0) && (bus_l1 != 0))))) && ((( !(13.0 <= bus_x)) || ( !((bus_l0 != 0) && ( !(bus_l1 != 0))))) && ((delta == 0.0) || ( !((bus_l0 != 0) && (bus_l1 != 0)))))) && (0.0 <= delta)))) && (delta == _diverge_delta));
  while (__ok) {
    _x__diverge_delta = __VERIFIER_nondet_float();
    _x_env_evt2 = __VERIFIER_nondet_bool();
    _x_env_evt1 = __VERIFIER_nondet_bool();
    _x_env_evt0 = __VERIFIER_nondet_bool();
    _x_st_l1 = __VERIFIER_nondet_bool();
    _x_st_l0 = __VERIFIER_nondet_bool();
    _x_delta = __VERIFIER_nondet_float();
    _x_bus_evt0 = __VERIFIER_nondet_bool();
    _x_bus_evt1 = __VERIFIER_nondet_bool();
    _x_st_x = __VERIFIER_nondet_float();
    _x_bus_l0 = __VERIFIER_nondet_bool();
    _x_bus_evt2 = __VERIFIER_nondet_bool();
    _x_bus_cd_id = __VERIFIER_nondet_bool();
    _x_st_evt0 = __VERIFIER_nondet_bool();
    _x_bus_l1 = __VERIFIER_nondet_bool();
    _x_st_backoff = __VERIFIER_nondet_float();
    _x_bus_x = __VERIFIER_nondet_float();
    _x_st_evt1 = __VERIFIER_nondet_bool();
    _x_st_evt2 = __VERIFIER_nondet_bool();

    __ok = ((((((((((((( !(_x_env_evt2 != 0)) && ((_x_env_evt0 != 0) && ( !(_x_env_evt1 != 0)))) || (((( !(_x_env_evt2 != 0)) && (( !(_x_env_evt0 != 0)) && ( !(_x_env_evt1 != 0)))) || ((_x_env_evt2 != 0) && (( !(_x_env_evt0 != 0)) && ( !(_x_env_evt1 != 0))))) || ((( !(_x_env_evt2 != 0)) && ((_x_env_evt1 != 0) && ( !(_x_env_evt0 != 0)))) || ((_x_env_evt2 != 0) && ((_x_env_evt1 != 0) && ( !(_x_env_evt0 != 0))))))) && (((((((((((((((((( !(_x_st_evt2 != 0)) && ((_x_st_evt0 != 0) && ( !(_x_st_evt1 != 0)))) || (((( !(_x_st_evt2 != 0)) && (( !(_x_st_evt0 != 0)) && ( !(_x_st_evt1 != 0)))) || ((_x_st_evt2 != 0) && (( !(_x_st_evt0 != 0)) && ( !(_x_st_evt1 != 0))))) || ((( !(_x_st_evt2 != 0)) && ((_x_st_evt1 != 0) && ( !(_x_st_evt0 != 0)))) || ((_x_st_evt2 != 0) && ((_x_st_evt1 != 0) && ( !(_x_st_evt0 != 0))))))) && ((( !(_x_st_l0 != 0)) && ( !(_x_st_l1 != 0))) || (((_x_st_l1 != 0) && ( !(_x_st_l0 != 0))) || ((_x_st_l0 != 0) && ( !(_x_st_l1 != 0)))))) && ((_x_st_x <= 404.0) || ( !((_x_st_l1 != 0) && ( !(_x_st_l0 != 0)))))) && (13.0 <= _x_st_backoff)) && (((((st_l0 != 0) == (_x_st_l0 != 0)) && ((st_l1 != 0) == (_x_st_l1 != 0))) && (((delta + (st_x + (-1.0 * _x_st_x))) == 0.0) && (st_backoff == _x_st_backoff))) || ( !(( !(delta <= 0.0)) || (( !(st_evt2 != 0)) && (( !(st_evt0 != 0)) && ( !(st_evt1 != 0)))))))) && (((((_x_st_l0 != 0) && ( !(_x_st_l1 != 0))) || ((( !(_x_st_l0 != 0)) && ( !(_x_st_l1 != 0))) || ((_x_st_l1 != 0) && ( !(_x_st_l0 != 0))))) && ((st_backoff == _x_st_backoff) && (_x_st_x == 0.0))) || ( !((( !(st_l0 != 0)) && ( !(st_l1 != 0))) && ((delta == 0.0) && ( !(( !(st_evt2 != 0)) && (( !(st_evt0 != 0)) && ( !(st_evt1 != 0)))))))))) && ((( !(st_evt2 != 0)) && ((st_evt0 != 0) && ( !(st_evt1 != 0)))) || ( !((( !(_x_st_l0 != 0)) && ( !(_x_st_l1 != 0))) && ((( !(st_l0 != 0)) && ( !(st_l1 != 0))) && ((delta == 0.0) && ( !(( !(st_evt2 != 0)) && (( !(st_evt0 != 0)) && ( !(st_evt1 != 0))))))))))) && (((st_evt2 != 0) && (( !(st_evt0 != 0)) && ( !(st_evt1 != 0)))) || ( !(((_x_st_l1 != 0) && ( !(_x_st_l0 != 0))) && ((( !(st_l0 != 0)) && ( !(st_l1 != 0))) && ((delta == 0.0) && ( !(( !(st_evt2 != 0)) && (( !(st_evt0 != 0)) && ( !(st_evt1 != 0))))))))))) && ((((st_evt2 != 0) && ((st_evt1 != 0) && ( !(st_evt0 != 0)))) || (( !(st_evt2 != 0)) && ((st_evt0 != 0) && ( !(st_evt1 != 0))))) || ( !(((_x_st_l0 != 0) && ( !(_x_st_l1 != 0))) && ((( !(st_l0 != 0)) && ( !(st_l1 != 0))) && ((delta == 0.0) && ( !(( !(st_evt2 != 0)) && (( !(st_evt0 != 0)) && ( !(st_evt1 != 0))))))))))) && (((_x_st_x == 0.0) && ((( !(_x_st_l0 != 0)) && ( !(_x_st_l1 != 0))) || ((_x_st_l0 != 0) && ( !(_x_st_l1 != 0))))) || ( !(((st_l1 != 0) && ( !(st_l0 != 0))) && ((delta == 0.0) && ( !(( !(st_evt2 != 0)) && (( !(st_evt0 != 0)) && ( !(st_evt1 != 0)))))))))) && (((404.0 <= st_x) && ((( !(st_evt2 != 0)) && ((st_evt1 != 0) && ( !(st_evt0 != 0)))) && (_x_st_backoff <= st_backoff))) || ( !((( !(_x_st_l0 != 0)) && ( !(_x_st_l1 != 0))) && (((st_l1 != 0) && ( !(st_l0 != 0))) && ((delta == 0.0) && ( !(( !(st_evt2 != 0)) && (( !(st_evt0 != 0)) && ( !(st_evt1 != 0))))))))))) && (((( !(st_evt2 != 0)) && ((st_evt0 != 0) && ( !(st_evt1 != 0)))) && ((st_backoff + (-1.0 * _x_st_backoff)) <= -1.0)) || ( !(((_x_st_l0 != 0) && ( !(_x_st_l1 != 0))) && (((st_l1 != 0) && ( !(st_l0 != 0))) && ((delta == 0.0) && ( !(( !(st_evt2 != 0)) && (( !(st_evt0 != 0)) && ( !(st_evt1 != 0))))))))))) && (((((_x_st_l1 != 0) && ( !(_x_st_l0 != 0))) || ((_x_st_l0 != 0) && ( !(_x_st_l1 != 0)))) && ((st_backoff == _x_st_backoff) && (_x_st_x == 0.0))) || ( !(((st_l0 != 0) && ( !(st_l1 != 0))) && ((delta == 0.0) && ( !(( !(st_evt2 != 0)) && (( !(st_evt0 != 0)) && ( !(st_evt1 != 0)))))))))) && ((( !(st_evt2 != 0)) && ((st_evt0 != 0) && ( !(st_evt1 != 0)))) || ( !(((_x_st_l0 != 0) && ( !(_x_st_l1 != 0))) && (((st_l0 != 0) && ( !(st_l1 != 0))) && ((delta == 0.0) && ( !(( !(st_evt2 != 0)) && (( !(st_evt0 != 0)) && ( !(st_evt1 != 0))))))))))) && ((((st_evt2 != 0) && (( !(st_evt0 != 0)) && ( !(st_evt1 != 0)))) && (st_backoff <= st_x)) || ( !(((_x_st_l1 != 0) && ( !(_x_st_l0 != 0))) && (((st_l0 != 0) && ( !(st_l1 != 0))) && ((delta == 0.0) && ( !(( !(st_evt2 != 0)) && (( !(st_evt0 != 0)) && ( !(st_evt1 != 0))))))))))) && (((((((((((((( !(_x_bus_evt2 != 0)) && (( !(_x_bus_evt0 != 0)) && ( !(_x_bus_evt1 != 0)))) || ((((_x_bus_evt2 != 0) && (( !(_x_bus_evt0 != 0)) && ( !(_x_bus_evt1 != 0)))) || (( !(_x_bus_evt2 != 0)) && ((_x_bus_evt1 != 0) && ( !(_x_bus_evt0 != 0))))) || (((_x_bus_evt2 != 0) && ((_x_bus_evt1 != 0) && ( !(_x_bus_evt0 != 0)))) || (( !(_x_bus_evt2 != 0)) && ((_x_bus_evt0 != 0) && ( !(_x_bus_evt1 != 0))))))) && (((( !(_x_bus_l0 != 0)) && ( !(_x_bus_l1 != 0))) || ((_x_bus_l1 != 0) && ( !(_x_bus_l0 != 0)))) || (((_x_bus_l0 != 0) && ( !(_x_bus_l1 != 0))) || ((_x_bus_l0 != 0) && (_x_bus_l1 != 0))))) && ((( !(13.0 <= _x_bus_x)) || ( !((_x_bus_l0 != 0) && ( !(_x_bus_l1 != 0))))) && ((_x_delta == 0.0) || ( !((_x_bus_l0 != 0) && (_x_bus_l1 != 0)))))) && ((((bus_cd_id != 0) == (_x_bus_cd_id != 0)) && ((((bus_l0 != 0) == (_x_bus_l0 != 0)) && ((bus_l1 != 0) == (_x_bus_l1 != 0))) && ((delta + (bus_x + (-1.0 * _x_bus_x))) == 0.0))) || ( !((( !(bus_evt2 != 0)) && (( !(bus_evt0 != 0)) && ( !(bus_evt1 != 0)))) || ( !(delta <= 0.0)))))) && (((((bus_evt2 != 0) && (( !(bus_evt0 != 0)) && ( !(bus_evt1 != 0)))) && ((_x_bus_l1 != 0) && ( !(_x_bus_l0 != 0)))) && (((bus_cd_id != 0) == (_x_bus_cd_id != 0)) && (_x_bus_x == 0.0))) || ( !((( !(bus_l0 != 0)) && ( !(bus_l1 != 0))) && ((delta == 0.0) && ( !(( !(bus_evt2 != 0)) && (( !(bus_evt0 != 0)) && ( !(bus_evt1 != 0)))))))))) && ((((_x_bus_l0 != 0) && ( !(_x_bus_l1 != 0))) || ((( !(_x_bus_l0 != 0)) && ( !(_x_bus_l1 != 0))) || ((_x_bus_l1 != 0) && ( !(_x_bus_l0 != 0))))) || ( !(((bus_l1 != 0) && ( !(bus_l0 != 0))) && ((delta == 0.0) && ( !(( !(bus_evt2 != 0)) && (( !(bus_evt0 != 0)) && ( !(bus_evt1 != 0)))))))))) && (((( !(bus_evt2 != 0)) && ((bus_evt1 != 0) && ( !(bus_evt0 != 0)))) && (((bus_cd_id != 0) == (_x_bus_cd_id != 0)) && (_x_bus_x == 0.0))) || ( !(((delta == 0.0) && ( !(( !(bus_evt2 != 0)) && (( !(bus_evt0 != 0)) && ( !(bus_evt1 != 0)))))) && ((( !(_x_bus_l0 != 0)) && ( !(_x_bus_l1 != 0))) && ((bus_l1 != 0) && ( !(bus_l0 != 0)))))))) && (((((bus_evt2 != 0) && ((bus_evt1 != 0) && ( !(bus_evt0 != 0)))) && (13.0 <= bus_x)) && (((bus_cd_id != 0) == (_x_bus_cd_id != 0)) && (bus_x == _x_bus_x))) || ( !(((delta == 0.0) && ( !(( !(bus_evt2 != 0)) && (( !(bus_evt0 != 0)) && ( !(bus_evt1 != 0)))))) && (((bus_l1 != 0) && ( !(bus_l0 != 0))) && ((_x_bus_l1 != 0) && ( !(_x_bus_l0 != 0)))))))) && ((((bus_evt2 != 0) && (( !(bus_evt0 != 0)) && ( !(bus_evt1 != 0)))) && (( !(13.0 <= bus_x)) && (_x_bus_x == 0.0))) || ( !(((delta == 0.0) && ( !(( !(bus_evt2 != 0)) && (( !(bus_evt0 != 0)) && ( !(bus_evt1 != 0)))))) && (((bus_l1 != 0) && ( !(bus_l0 != 0))) && ((_x_bus_l0 != 0) && ( !(_x_bus_l1 != 0)))))))) && ((((((_x_bus_l0 != 0) && (_x_bus_l1 != 0)) && ( !(13.0 <= bus_x))) && ((( !(bus_evt2 != 0)) && ((bus_evt0 != 0) && ( !(bus_evt1 != 0)))) && (_x_bus_x == 0.0))) && ( !((bus_cd_id != 0) == (_x_bus_cd_id != 0)))) || ( !(((bus_l0 != 0) && ( !(bus_l1 != 0))) && ((delta == 0.0) && ( !(( !(bus_evt2 != 0)) && (( !(bus_evt0 != 0)) && ( !(bus_evt1 != 0)))))))))) && (((( !(_x_bus_l0 != 0)) && ( !(_x_bus_l1 != 0))) && (((bus_cd_id != 0) == (_x_bus_cd_id != 0)) && (_x_bus_x == 0.0))) || ( !(((bus_l0 != 0) && (bus_l1 != 0)) && ((delta == 0.0) && ( !(( !(bus_evt2 != 0)) && (( !(bus_evt0 != 0)) && ( !(bus_evt1 != 0)))))))))) && (0.0 <= _x_delta)))) && ((( !(st_evt2 != 0)) && (( !(st_evt0 != 0)) && ( !(st_evt1 != 0)))) || (( !(env_evt2 != 0)) && (( !(env_evt0 != 0)) && ( !(env_evt1 != 0)))))) && ((( !(( !(bus_evt2 != 0)) && (( !(bus_evt0 != 0)) && ( !(bus_evt1 != 0))))) || (( !(( !(st_evt2 != 0)) && (( !(st_evt0 != 0)) && ( !(st_evt1 != 0))))) || ( !(( !(env_evt2 != 0)) && (( !(env_evt0 != 0)) && ( !(env_evt1 != 0))))))) || ( !(delta == 0.0)))) && (( !(delta == 0.0)) || (((bus_evt2 != 0) && (( !(bus_evt0 != 0)) && ( !(bus_evt1 != 0)))) == (((st_evt2 != 0) && (( !(st_evt0 != 0)) && ( !(st_evt1 != 0)))) || ((env_evt2 != 0) && (( !(env_evt0 != 0)) && ( !(env_evt1 != 0)))))))) && (( !(delta == 0.0)) || ((( !(bus_evt2 != 0)) && ((bus_evt1 != 0) && ( !(bus_evt0 != 0)))) == ((( !(st_evt2 != 0)) && ((st_evt1 != 0) && ( !(st_evt0 != 0)))) || (( !(env_evt2 != 0)) && ((env_evt1 != 0) && ( !(env_evt0 != 0)))))))) && (( !(delta == 0.0)) || (((bus_evt2 != 0) && ((bus_evt1 != 0) && ( !(bus_evt0 != 0)))) == (((st_evt2 != 0) && ((st_evt1 != 0) && ( !(st_evt0 != 0)))) || ((env_evt2 != 0) && ((env_evt1 != 0) && ( !(env_evt0 != 0)))))))) && (( !(delta == 0.0)) || ((( !(bus_evt2 != 0)) && ((bus_evt0 != 0) && ( !(bus_evt1 != 0)))) == ((( !(st_evt2 != 0)) && ((st_evt0 != 0) && ( !(st_evt1 != 0)))) || (( !(env_evt2 != 0)) && ((env_evt0 != 0) && ( !(env_evt1 != 0)))))))) && (( !(delta == 0.0)) || ((( !(st_evt2 != 0)) && ((st_evt0 != 0) && ( !(st_evt1 != 0)))) == ((( !(bus_evt2 != 0)) && ((bus_evt0 != 0) && ( !(bus_evt1 != 0)))) && (bus_cd_id != 0))))) && (( !(delta == 0.0)) || ((( !(env_evt2 != 0)) && ((env_evt0 != 0) && ( !(env_evt1 != 0)))) == ((( !(bus_evt2 != 0)) && ((bus_evt0 != 0) && ( !(bus_evt1 != 0)))) && ( !(bus_cd_id != 0)))))) && (((delta == _x__diverge_delta) || ( !(1.0 <= _diverge_delta))) && ((1.0 <= _diverge_delta) || ((delta + (_diverge_delta + (-1.0 * _x__diverge_delta))) == 0.0))));
    _diverge_delta = _x__diverge_delta;
    env_evt2 = _x_env_evt2;
    env_evt1 = _x_env_evt1;
    env_evt0 = _x_env_evt0;
    st_l1 = _x_st_l1;
    st_l0 = _x_st_l0;
    delta = _x_delta;
    bus_evt0 = _x_bus_evt0;
    bus_evt1 = _x_bus_evt1;
    st_x = _x_st_x;
    bus_l0 = _x_bus_l0;
    bus_evt2 = _x_bus_evt2;
    bus_cd_id = _x_bus_cd_id;
    st_evt0 = _x_st_evt0;
    bus_l1 = _x_bus_l1;
    st_backoff = _x_st_backoff;
    bus_x = _x_bus_x;
    st_evt1 = _x_st_evt1;
    st_evt2 = _x_st_evt2;

  }
}
