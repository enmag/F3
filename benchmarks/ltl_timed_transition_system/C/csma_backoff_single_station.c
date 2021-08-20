extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);
typedef enum {false, true} bool;
bool __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}

int main()
{
bool _J465, _x__J465;
float _diverge_delta, _x__diverge_delta;
float delta, _x_delta;
bool _EL_U_428, _x__EL_U_428;
bool bus_l1, _x_bus_l1;
bool bus_l0, _x_bus_l0;
bool _EL_U_430, _x__EL_U_430;
bool _EL_U_432, _x__EL_U_432;
bool _EL_U_434, _x__EL_U_434;
bool _EL_U_436, _x__EL_U_436;
float bus_x, _x_bus_x;
bool _EL_U_438, _x__EL_U_438;
bool bus_evt1, _x_bus_evt1;
bool bus_evt0, _x_bus_evt0;
bool bus_evt2, _x_bus_evt2;
bool bus_cd_id, _x_bus_cd_id;
bool st_l0, _x_st_l0;
bool st_l1, _x_st_l1;
float st_x, _x_st_x;
bool st_evt0, _x_st_evt0;
bool st_evt1, _x_st_evt1;
bool st_evt2, _x_st_evt2;
float st_backoff, _x_st_backoff;
bool env_evt0, _x_env_evt0;
bool env_evt1, _x_env_evt1;
bool env_evt2, _x_env_evt2;
bool _J495, _x__J495;
bool _J489, _x__J489;
bool _J482, _x__J482;
bool _J476, _x__J476;
bool _J471, _x__J471;

  int __steps_to_fair = __VERIFIER_nondet_int();
  _J465 = __VERIFIER_nondet_bool();
  _diverge_delta = __VERIFIER_nondet_float();
  delta = __VERIFIER_nondet_float();
  _EL_U_428 = __VERIFIER_nondet_bool();
  bus_l1 = __VERIFIER_nondet_bool();
  bus_l0 = __VERIFIER_nondet_bool();
  _EL_U_430 = __VERIFIER_nondet_bool();
  _EL_U_432 = __VERIFIER_nondet_bool();
  _EL_U_434 = __VERIFIER_nondet_bool();
  _EL_U_436 = __VERIFIER_nondet_bool();
  bus_x = __VERIFIER_nondet_float();
  _EL_U_438 = __VERIFIER_nondet_bool();
  bus_evt1 = __VERIFIER_nondet_bool();
  bus_evt0 = __VERIFIER_nondet_bool();
  bus_evt2 = __VERIFIER_nondet_bool();
  bus_cd_id = __VERIFIER_nondet_bool();
  st_l0 = __VERIFIER_nondet_bool();
  st_l1 = __VERIFIER_nondet_bool();
  st_x = __VERIFIER_nondet_float();
  st_evt0 = __VERIFIER_nondet_bool();
  st_evt1 = __VERIFIER_nondet_bool();
  st_evt2 = __VERIFIER_nondet_bool();
  st_backoff = __VERIFIER_nondet_float();
  env_evt0 = __VERIFIER_nondet_bool();
  env_evt1 = __VERIFIER_nondet_bool();
  env_evt2 = __VERIFIER_nondet_bool();
  _J495 = __VERIFIER_nondet_bool();
  _J489 = __VERIFIER_nondet_bool();
  _J482 = __VERIFIER_nondet_bool();
  _J476 = __VERIFIER_nondet_bool();
  _J471 = __VERIFIER_nondet_bool();

  bool __ok = (((((( !env_evt2) && (env_evt0 && ( !env_evt1))) || (((( !env_evt2) && (( !env_evt0) && ( !env_evt1))) || (env_evt2 && (( !env_evt0) && ( !env_evt1)))) || ((( !env_evt2) && (env_evt1 && ( !env_evt0))) || (env_evt2 && (env_evt1 && ( !env_evt0)))))) && (((((((( !st_l0) && ( !st_l1)) && (st_x == 0.0)) && (13.0 <= st_backoff)) && ((( !st_evt2) && (st_evt0 && ( !st_evt1))) || (((( !st_evt2) && (( !st_evt0) && ( !st_evt1))) || (st_evt2 && (( !st_evt0) && ( !st_evt1)))) || ((( !st_evt2) && (st_evt1 && ( !st_evt0))) || (st_evt2 && (st_evt1 && ( !st_evt0))))))) && ((( !st_l0) && ( !st_l1)) || ((st_l1 && ( !st_l0)) || (st_l0 && ( !st_l1))))) && ((st_x <= 404.0) || ( !(st_l1 && ( !st_l0))))) && ((((((( !bus_l0) && ( !bus_l1)) && (bus_cd_id && (bus_x == 0.0))) && ((( !bus_evt2) && (( !bus_evt0) && ( !bus_evt1))) || (((bus_evt2 && (( !bus_evt0) && ( !bus_evt1))) || (( !bus_evt2) && (bus_evt1 && ( !bus_evt0)))) || ((bus_evt2 && (bus_evt1 && ( !bus_evt0))) || (( !bus_evt2) && (bus_evt0 && ( !bus_evt1))))))) && (((( !bus_l0) && ( !bus_l1)) || (bus_l1 && ( !bus_l0))) || ((bus_l0 && ( !bus_l1)) || (bus_l0 && bus_l1)))) && ((( !(13.0 <= bus_x)) || ( !(bus_l0 && ( !bus_l1)))) && ((delta == 0.0) || ( !(bus_l0 && bus_l1))))) && (0.0 <= delta)))) && (delta == _diverge_delta)) && ((((((( !((( !(_EL_U_438 || ( !((( !st_l0) && ( !st_l1)) || _EL_U_436)))) || (_EL_U_434 || ( !((st_l1 && ( !st_l0)) || _EL_U_432)))) || (_EL_U_430 || ( !((1.0 <= _diverge_delta) || _EL_U_428))))) && ( !_J465)) && ( !_J471)) && ( !_J476)) && ( !_J482)) && ( !_J489)) && ( !_J495)));
  while (__steps_to_fair >= 0 && __ok) {
    if ((((((_J465 && _J471) && _J476) && _J482) && _J489) && _J495)) {
      __steps_to_fair = __VERIFIER_nondet_int();
    } else {
      __steps_to_fair--;
    }
    _x__J465 = __VERIFIER_nondet_bool();
    _x__diverge_delta = __VERIFIER_nondet_float();
    _x_delta = __VERIFIER_nondet_float();
    _x__EL_U_428 = __VERIFIER_nondet_bool();
    _x_bus_l1 = __VERIFIER_nondet_bool();
    _x_bus_l0 = __VERIFIER_nondet_bool();
    _x__EL_U_430 = __VERIFIER_nondet_bool();
    _x__EL_U_432 = __VERIFIER_nondet_bool();
    _x__EL_U_434 = __VERIFIER_nondet_bool();
    _x__EL_U_436 = __VERIFIER_nondet_bool();
    _x_bus_x = __VERIFIER_nondet_float();
    _x__EL_U_438 = __VERIFIER_nondet_bool();
    _x_bus_evt1 = __VERIFIER_nondet_bool();
    _x_bus_evt0 = __VERIFIER_nondet_bool();
    _x_bus_evt2 = __VERIFIER_nondet_bool();
    _x_bus_cd_id = __VERIFIER_nondet_bool();
    _x_st_l0 = __VERIFIER_nondet_bool();
    _x_st_l1 = __VERIFIER_nondet_bool();
    _x_st_x = __VERIFIER_nondet_float();
    _x_st_evt0 = __VERIFIER_nondet_bool();
    _x_st_evt1 = __VERIFIER_nondet_bool();
    _x_st_evt2 = __VERIFIER_nondet_bool();
    _x_st_backoff = __VERIFIER_nondet_float();
    _x_env_evt0 = __VERIFIER_nondet_bool();
    _x_env_evt1 = __VERIFIER_nondet_bool();
    _x_env_evt2 = __VERIFIER_nondet_bool();
    _x__J495 = __VERIFIER_nondet_bool();
    _x__J489 = __VERIFIER_nondet_bool();
    _x__J482 = __VERIFIER_nondet_bool();
    _x__J476 = __VERIFIER_nondet_bool();
    _x__J471 = __VERIFIER_nondet_bool();

    __ok = (((((((((((((( !_x_env_evt2) && (_x_env_evt0 && ( !_x_env_evt1))) || (((( !_x_env_evt2) && (( !_x_env_evt0) && ( !_x_env_evt1))) || (_x_env_evt2 && (( !_x_env_evt0) && ( !_x_env_evt1)))) || ((( !_x_env_evt2) && (_x_env_evt1 && ( !_x_env_evt0))) || (_x_env_evt2 && (_x_env_evt1 && ( !_x_env_evt0)))))) && (((((((((((((((((( !_x_st_evt2) && (_x_st_evt0 && ( !_x_st_evt1))) || (((( !_x_st_evt2) && (( !_x_st_evt0) && ( !_x_st_evt1))) || (_x_st_evt2 && (( !_x_st_evt0) && ( !_x_st_evt1)))) || ((( !_x_st_evt2) && (_x_st_evt1 && ( !_x_st_evt0))) || (_x_st_evt2 && (_x_st_evt1 && ( !_x_st_evt0)))))) && ((( !_x_st_l0) && ( !_x_st_l1)) || ((_x_st_l1 && ( !_x_st_l0)) || (_x_st_l0 && ( !_x_st_l1))))) && ((_x_st_x <= 404.0) || ( !(_x_st_l1 && ( !_x_st_l0))))) && (13.0 <= _x_st_backoff)) && ((((st_l0 == _x_st_l0) && (st_l1 == _x_st_l1)) && (((delta + (st_x + (-1.0 * _x_st_x))) == 0.0) && (st_backoff == _x_st_backoff))) || ( !(( !(delta <= 0.0)) || (( !st_evt2) && (( !st_evt0) && ( !st_evt1))))))) && ((((_x_st_l0 && ( !_x_st_l1)) || ((( !_x_st_l0) && ( !_x_st_l1)) || (_x_st_l1 && ( !_x_st_l0)))) && ((st_backoff == _x_st_backoff) && (_x_st_x == 0.0))) || ( !((( !st_l0) && ( !st_l1)) && ((delta == 0.0) && ( !(( !st_evt2) && (( !st_evt0) && ( !st_evt1))))))))) && ((( !st_evt2) && (st_evt0 && ( !st_evt1))) || ( !((( !_x_st_l0) && ( !_x_st_l1)) && ((( !st_l0) && ( !st_l1)) && ((delta == 0.0) && ( !(( !st_evt2) && (( !st_evt0) && ( !st_evt1)))))))))) && ((st_evt2 && (( !st_evt0) && ( !st_evt1))) || ( !((_x_st_l1 && ( !_x_st_l0)) && ((( !st_l0) && ( !st_l1)) && ((delta == 0.0) && ( !(( !st_evt2) && (( !st_evt0) && ( !st_evt1)))))))))) && (((st_evt2 && (st_evt1 && ( !st_evt0))) || (( !st_evt2) && (st_evt0 && ( !st_evt1)))) || ( !((_x_st_l0 && ( !_x_st_l1)) && ((( !st_l0) && ( !st_l1)) && ((delta == 0.0) && ( !(( !st_evt2) && (( !st_evt0) && ( !st_evt1)))))))))) && (((_x_st_x == 0.0) && ((( !_x_st_l0) && ( !_x_st_l1)) || (_x_st_l0 && ( !_x_st_l1)))) || ( !((st_l1 && ( !st_l0)) && ((delta == 0.0) && ( !(( !st_evt2) && (( !st_evt0) && ( !st_evt1))))))))) && (((404.0 <= st_x) && ((( !st_evt2) && (st_evt1 && ( !st_evt0))) && (_x_st_backoff <= st_backoff))) || ( !((( !_x_st_l0) && ( !_x_st_l1)) && ((st_l1 && ( !st_l0)) && ((delta == 0.0) && ( !(( !st_evt2) && (( !st_evt0) && ( !st_evt1)))))))))) && (((( !st_evt2) && (st_evt0 && ( !st_evt1))) && ((st_backoff + (-1.0 * _x_st_backoff)) <= -1.0)) || ( !((_x_st_l0 && ( !_x_st_l1)) && ((st_l1 && ( !st_l0)) && ((delta == 0.0) && ( !(( !st_evt2) && (( !st_evt0) && ( !st_evt1)))))))))) && ((((_x_st_l1 && ( !_x_st_l0)) || (_x_st_l0 && ( !_x_st_l1))) && ((st_backoff == _x_st_backoff) && (_x_st_x == 0.0))) || ( !((st_l0 && ( !st_l1)) && ((delta == 0.0) && ( !(( !st_evt2) && (( !st_evt0) && ( !st_evt1))))))))) && ((( !st_evt2) && (st_evt0 && ( !st_evt1))) || ( !((_x_st_l0 && ( !_x_st_l1)) && ((st_l0 && ( !st_l1)) && ((delta == 0.0) && ( !(( !st_evt2) && (( !st_evt0) && ( !st_evt1)))))))))) && (((st_evt2 && (( !st_evt0) && ( !st_evt1))) && (st_backoff <= st_x)) || ( !((_x_st_l1 && ( !_x_st_l0)) && ((st_l0 && ( !st_l1)) && ((delta == 0.0) && ( !(( !st_evt2) && (( !st_evt0) && ( !st_evt1)))))))))) && (((((((((((((( !_x_bus_evt2) && (( !_x_bus_evt0) && ( !_x_bus_evt1))) || (((_x_bus_evt2 && (( !_x_bus_evt0) && ( !_x_bus_evt1))) || (( !_x_bus_evt2) && (_x_bus_evt1 && ( !_x_bus_evt0)))) || ((_x_bus_evt2 && (_x_bus_evt1 && ( !_x_bus_evt0))) || (( !_x_bus_evt2) && (_x_bus_evt0 && ( !_x_bus_evt1)))))) && (((( !_x_bus_l0) && ( !_x_bus_l1)) || (_x_bus_l1 && ( !_x_bus_l0))) || ((_x_bus_l0 && ( !_x_bus_l1)) || (_x_bus_l0 && _x_bus_l1)))) && ((( !(13.0 <= _x_bus_x)) || ( !(_x_bus_l0 && ( !_x_bus_l1)))) && ((_x_delta == 0.0) || ( !(_x_bus_l0 && _x_bus_l1))))) && (((bus_cd_id == _x_bus_cd_id) && (((bus_l0 == _x_bus_l0) && (bus_l1 == _x_bus_l1)) && ((delta + (bus_x + (-1.0 * _x_bus_x))) == 0.0))) || ( !((( !bus_evt2) && (( !bus_evt0) && ( !bus_evt1))) || ( !(delta <= 0.0)))))) && ((((bus_evt2 && (( !bus_evt0) && ( !bus_evt1))) && (_x_bus_l1 && ( !_x_bus_l0))) && ((bus_cd_id == _x_bus_cd_id) && (_x_bus_x == 0.0))) || ( !((( !bus_l0) && ( !bus_l1)) && ((delta == 0.0) && ( !(( !bus_evt2) && (( !bus_evt0) && ( !bus_evt1))))))))) && (((_x_bus_l0 && ( !_x_bus_l1)) || ((( !_x_bus_l0) && ( !_x_bus_l1)) || (_x_bus_l1 && ( !_x_bus_l0)))) || ( !((bus_l1 && ( !bus_l0)) && ((delta == 0.0) && ( !(( !bus_evt2) && (( !bus_evt0) && ( !bus_evt1))))))))) && (((( !bus_evt2) && (bus_evt1 && ( !bus_evt0))) && ((bus_cd_id == _x_bus_cd_id) && (_x_bus_x == 0.0))) || ( !(((delta == 0.0) && ( !(( !bus_evt2) && (( !bus_evt0) && ( !bus_evt1))))) && ((( !_x_bus_l0) && ( !_x_bus_l1)) && (bus_l1 && ( !bus_l0))))))) && ((((bus_evt2 && (bus_evt1 && ( !bus_evt0))) && (13.0 <= bus_x)) && ((bus_cd_id == _x_bus_cd_id) && (bus_x == _x_bus_x))) || ( !(((delta == 0.0) && ( !(( !bus_evt2) && (( !bus_evt0) && ( !bus_evt1))))) && ((bus_l1 && ( !bus_l0)) && (_x_bus_l1 && ( !_x_bus_l0))))))) && (((bus_evt2 && (( !bus_evt0) && ( !bus_evt1))) && (( !(13.0 <= bus_x)) && (_x_bus_x == 0.0))) || ( !(((delta == 0.0) && ( !(( !bus_evt2) && (( !bus_evt0) && ( !bus_evt1))))) && ((bus_l1 && ( !bus_l0)) && (_x_bus_l0 && ( !_x_bus_l1))))))) && (((((_x_bus_l0 && _x_bus_l1) && ( !(13.0 <= bus_x))) && ((( !bus_evt2) && (bus_evt0 && ( !bus_evt1))) && (_x_bus_x == 0.0))) && ( !(bus_cd_id == _x_bus_cd_id))) || ( !((bus_l0 && ( !bus_l1)) && ((delta == 0.0) && ( !(( !bus_evt2) && (( !bus_evt0) && ( !bus_evt1))))))))) && (((( !_x_bus_l0) && ( !_x_bus_l1)) && ((bus_cd_id == _x_bus_cd_id) && (_x_bus_x == 0.0))) || ( !((bus_l0 && bus_l1) && ((delta == 0.0) && ( !(( !bus_evt2) && (( !bus_evt0) && ( !bus_evt1))))))))) && (0.0 <= _x_delta)))) && ((( !st_evt2) && (( !st_evt0) && ( !st_evt1))) || (( !env_evt2) && (( !env_evt0) && ( !env_evt1))))) && ((( !(( !bus_evt2) && (( !bus_evt0) && ( !bus_evt1)))) || (( !(( !st_evt2) && (( !st_evt0) && ( !st_evt1)))) || ( !(( !env_evt2) && (( !env_evt0) && ( !env_evt1)))))) || ( !(delta == 0.0)))) && (( !(delta == 0.0)) || ((bus_evt2 && (( !bus_evt0) && ( !bus_evt1))) == ((st_evt2 && (( !st_evt0) && ( !st_evt1))) || (env_evt2 && (( !env_evt0) && ( !env_evt1))))))) && (( !(delta == 0.0)) || ((( !bus_evt2) && (bus_evt1 && ( !bus_evt0))) == ((( !st_evt2) && (st_evt1 && ( !st_evt0))) || (( !env_evt2) && (env_evt1 && ( !env_evt0))))))) && (( !(delta == 0.0)) || ((bus_evt2 && (bus_evt1 && ( !bus_evt0))) == ((st_evt2 && (st_evt1 && ( !st_evt0))) || (env_evt2 && (env_evt1 && ( !env_evt0))))))) && (( !(delta == 0.0)) || ((( !bus_evt2) && (bus_evt0 && ( !bus_evt1))) == ((( !st_evt2) && (st_evt0 && ( !st_evt1))) || (( !env_evt2) && (env_evt0 && ( !env_evt1))))))) && (( !(delta == 0.0)) || ((( !st_evt2) && (st_evt0 && ( !st_evt1))) == ((( !bus_evt2) && (bus_evt0 && ( !bus_evt1))) && bus_cd_id)))) && (( !(delta == 0.0)) || ((( !env_evt2) && (env_evt0 && ( !env_evt1))) == ((( !bus_evt2) && (bus_evt0 && ( !bus_evt1))) && ( !bus_cd_id))))) && (((delta == _x__diverge_delta) || ( !(1.0 <= _diverge_delta))) && ((1.0 <= _diverge_delta) || ((delta + (_diverge_delta + (-1.0 * _x__diverge_delta))) == 0.0)))) && ((((((((_EL_U_430 == (_x__EL_U_430 || ( !(_x__EL_U_428 || (1.0 <= _x__diverge_delta))))) && ((_EL_U_428 == (_x__EL_U_428 || (1.0 <= _x__diverge_delta))) && ((_EL_U_434 == (_x__EL_U_434 || ( !((_x_st_l1 && ( !_x_st_l0)) || _x__EL_U_432)))) && ((_EL_U_432 == ((_x_st_l1 && ( !_x_st_l0)) || _x__EL_U_432)) && ((_EL_U_436 == ((( !_x_st_l0) && ( !_x_st_l1)) || _x__EL_U_436)) && (_EL_U_438 == (_x__EL_U_438 || ( !((( !_x_st_l0) && ( !_x_st_l1)) || _x__EL_U_436))))))))) && (_x__J465 == (( !(((((_J465 && _J471) && _J476) && _J482) && _J489) && _J495)) && ((((((_J465 && _J471) && _J476) && _J482) && _J489) && _J495) || (((( !st_l0) && ( !st_l1)) || ( !((( !st_l0) && ( !st_l1)) || _EL_U_436))) || _J465))))) && (_x__J471 == (( !(((((_J465 && _J471) && _J476) && _J482) && _J489) && _J495)) && ((((((_J465 && _J471) && _J476) && _J482) && _J489) && _J495) || ((( !((( !st_l0) && ( !st_l1)) || _EL_U_436)) || ( !(_EL_U_438 || ( !((( !st_l0) && ( !st_l1)) || _EL_U_436))))) || _J471))))) && (_x__J476 == (( !(((((_J465 && _J471) && _J476) && _J482) && _J489) && _J495)) && ((((((_J465 && _J471) && _J476) && _J482) && _J489) && _J495) || (((st_l1 && ( !st_l0)) || ( !((st_l1 && ( !st_l0)) || _EL_U_432))) || _J476))))) && (_x__J482 == (( !(((((_J465 && _J471) && _J476) && _J482) && _J489) && _J495)) && ((((((_J465 && _J471) && _J476) && _J482) && _J489) && _J495) || ((( !((st_l1 && ( !st_l0)) || _EL_U_432)) || ( !(_EL_U_434 || ( !((st_l1 && ( !st_l0)) || _EL_U_432))))) || _J482))))) && (_x__J489 == (( !(((((_J465 && _J471) && _J476) && _J482) && _J489) && _J495)) && ((((((_J465 && _J471) && _J476) && _J482) && _J489) && _J495) || (((1.0 <= _diverge_delta) || ( !((1.0 <= _diverge_delta) || _EL_U_428))) || _J489))))) && (_x__J495 == (( !(((((_J465 && _J471) && _J476) && _J482) && _J489) && _J495)) && ((((((_J465 && _J471) && _J476) && _J482) && _J489) && _J495) || ((( !((1.0 <= _diverge_delta) || _EL_U_428)) || ( !(_EL_U_430 || ( !((1.0 <= _diverge_delta) || _EL_U_428))))) || _J495))))));
    _J465 = _x__J465;
    _diverge_delta = _x__diverge_delta;
    delta = _x_delta;
    _EL_U_428 = _x__EL_U_428;
    bus_l1 = _x_bus_l1;
    bus_l0 = _x_bus_l0;
    _EL_U_430 = _x__EL_U_430;
    _EL_U_432 = _x__EL_U_432;
    _EL_U_434 = _x__EL_U_434;
    _EL_U_436 = _x__EL_U_436;
    bus_x = _x_bus_x;
    _EL_U_438 = _x__EL_U_438;
    bus_evt1 = _x_bus_evt1;
    bus_evt0 = _x_bus_evt0;
    bus_evt2 = _x_bus_evt2;
    bus_cd_id = _x_bus_cd_id;
    st_l0 = _x_st_l0;
    st_l1 = _x_st_l1;
    st_x = _x_st_x;
    st_evt0 = _x_st_evt0;
    st_evt1 = _x_st_evt1;
    st_evt2 = _x_st_evt2;
    st_backoff = _x_st_backoff;
    env_evt0 = _x_env_evt0;
    env_evt1 = _x_env_evt1;
    env_evt2 = _x_env_evt2;
    _J495 = _x__J495;
    _J489 = _x__J489;
    _J482 = _x__J482;
    _J476 = _x__J476;
    _J471 = _x__J471;

  }
}
