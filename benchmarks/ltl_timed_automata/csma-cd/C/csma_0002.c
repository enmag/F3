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
bool bus_l1, _x_bus_l1;
bool bus_l0, _x_bus_l0;
bool _J603, _x__J603;
float bus_x, _x_bus_x;
bool _J597, _x__J597;
bool _J591, _x__J591;
bool _J582, _x__J582;
bool _EL_U_555, _x__EL_U_555;
int bus_j, _x_bus_j;
bool _EL_U_557, _x__EL_U_557;
bool _EL_U_559, _x__EL_U_559;
bool bus_evt1, _x_bus_evt1;
bool bus_evt0, _x_bus_evt0;
bool _EL_U_562, _x__EL_U_562;
bool bus_evt2, _x_bus_evt2;
bool s0_l1, _x_s0_l1;
int bus_cd_id, _x_bus_cd_id;
bool s0_l0, _x_s0_l0;
float s0_x, _x_s0_x;
bool s0_evt0, _x_s0_evt0;
bool s0_evt1, _x_s0_evt1;
bool s0_evt2, _x_s0_evt2;
bool s1_l1, _x_s1_l1;
bool s1_l0, _x_s1_l0;
float s1_x, _x_s1_x;
bool s1_evt0, _x_s1_evt0;
bool s1_evt1, _x_s1_evt1;
bool s1_evt2, _x_s1_evt2;

  int __steps_to_fair = __VERIFIER_nondet_int();
  _diverge_delta = __VERIFIER_nondet_float();
  delta = __VERIFIER_nondet_float();
  bus_l1 = __VERIFIER_nondet_bool();
  bus_l0 = __VERIFIER_nondet_bool();
  _J603 = __VERIFIER_nondet_bool();
  bus_x = __VERIFIER_nondet_float();
  _J597 = __VERIFIER_nondet_bool();
  _J591 = __VERIFIER_nondet_bool();
  _J582 = __VERIFIER_nondet_bool();
  _EL_U_555 = __VERIFIER_nondet_bool();
  bus_j = __VERIFIER_nondet_int();
  _EL_U_557 = __VERIFIER_nondet_bool();
  _EL_U_559 = __VERIFIER_nondet_bool();
  bus_evt1 = __VERIFIER_nondet_bool();
  bus_evt0 = __VERIFIER_nondet_bool();
  _EL_U_562 = __VERIFIER_nondet_bool();
  bus_evt2 = __VERIFIER_nondet_bool();
  s0_l1 = __VERIFIER_nondet_bool();
  bus_cd_id = __VERIFIER_nondet_int();
  s0_l0 = __VERIFIER_nondet_bool();
  s0_x = __VERIFIER_nondet_float();
  s0_evt0 = __VERIFIER_nondet_bool();
  s0_evt1 = __VERIFIER_nondet_bool();
  s0_evt2 = __VERIFIER_nondet_bool();
  s1_l1 = __VERIFIER_nondet_bool();
  s1_l0 = __VERIFIER_nondet_bool();
  s1_x = __VERIFIER_nondet_float();
  s1_evt0 = __VERIFIER_nondet_bool();
  s1_evt1 = __VERIFIER_nondet_bool();
  s1_evt2 = __VERIFIER_nondet_bool();

  bool __ok = (((((((((( !s1_l0) && ( !s1_l1)) && (s1_x == 0.0)) && ((( !s1_evt2) && (s1_evt0 && ( !s1_evt1))) || (((( !s1_evt2) && (( !s1_evt0) && ( !s1_evt1))) || (s1_evt2 && (( !s1_evt0) && ( !s1_evt1)))) || ((( !s1_evt2) && (s1_evt1 && ( !s1_evt0))) || (s1_evt2 && (s1_evt1 && ( !s1_evt0))))))) && ((( !s1_l0) && ( !s1_l1)) || ((s1_l1 && ( !s1_l0)) || (s1_l0 && ( !s1_l1))))) && ((s1_x <= 404.0) || ( !(s1_l1 && ( !s1_l0))))) && ((s1_x <= 26.0) || ( !(s1_l0 && ( !s1_l1))))) && (((((((( !s0_l0) && ( !s0_l1)) && (s0_x == 0.0)) && ((( !s0_evt2) && (s0_evt0 && ( !s0_evt1))) || (((( !s0_evt2) && (( !s0_evt0) && ( !s0_evt1))) || (s0_evt2 && (( !s0_evt0) && ( !s0_evt1)))) || ((( !s0_evt2) && (s0_evt1 && ( !s0_evt0))) || (s0_evt2 && (s0_evt1 && ( !s0_evt0))))))) && ((( !s0_l0) && ( !s0_l1)) || ((s0_l1 && ( !s0_l0)) || (s0_l0 && ( !s0_l1))))) && ((s0_x <= 404.0) || ( !(s0_l1 && ( !s0_l0))))) && ((s0_x <= 26.0) || ( !(s0_l0 && ( !s0_l1))))) && (((((( !bus_l0) && ( !bus_l1)) && (((( !bus_evt2) && (( !bus_evt0) && ( !bus_evt1))) || (((bus_evt2 && (( !bus_evt0) && ( !bus_evt1))) || (( !bus_evt2) && (bus_evt1 && ( !bus_evt0)))) || ((bus_evt2 && (bus_evt1 && ( !bus_evt0))) || (( !bus_evt2) && (bus_evt0 && ( !bus_evt1)))))) && (((( !bus_l0) && ( !bus_l1)) || (bus_l1 && ( !bus_l0))) || ((bus_l0 && ( !bus_l1)) || (bus_l0 && bus_l1))))) && ((bus_j == 0) && (bus_x == 0.0))) && ((( !(13.0 <= bus_x)) || ( !(bus_l0 && ( !bus_l1)))) && ((delta == 0.0) || ( !(bus_l0 && bus_l1))))) && (0.0 <= delta)))) && (delta == _diverge_delta)) && ((((( !(( !(_EL_U_562 || ( !(( !(s0_l1 && ( !s0_l0))) || ((( !s0_l0) && ( !s0_l1)) || _EL_U_559))))) || (_EL_U_557 || ( !((1.0 <= _diverge_delta) || _EL_U_555))))) && ( !_J582)) && ( !_J591)) && ( !_J597)) && ( !_J603)));
  while (__steps_to_fair >= 0 && __ok) {
    if ((((_J582 && _J591) && _J597) && _J603)) {
      __steps_to_fair = __VERIFIER_nondet_int();
    } else {
      __steps_to_fair--;
    }
    _x__diverge_delta = __VERIFIER_nondet_float();
    _x_delta = __VERIFIER_nondet_float();
    _x_bus_l1 = __VERIFIER_nondet_bool();
    _x_bus_l0 = __VERIFIER_nondet_bool();
    _x__J603 = __VERIFIER_nondet_bool();
    _x_bus_x = __VERIFIER_nondet_float();
    _x__J597 = __VERIFIER_nondet_bool();
    _x__J591 = __VERIFIER_nondet_bool();
    _x__J582 = __VERIFIER_nondet_bool();
    _x__EL_U_555 = __VERIFIER_nondet_bool();
    _x_bus_j = __VERIFIER_nondet_int();
    _x__EL_U_557 = __VERIFIER_nondet_bool();
    _x__EL_U_559 = __VERIFIER_nondet_bool();
    _x_bus_evt1 = __VERIFIER_nondet_bool();
    _x_bus_evt0 = __VERIFIER_nondet_bool();
    _x__EL_U_562 = __VERIFIER_nondet_bool();
    _x_bus_evt2 = __VERIFIER_nondet_bool();
    _x_s0_l1 = __VERIFIER_nondet_bool();
    _x_bus_cd_id = __VERIFIER_nondet_int();
    _x_s0_l0 = __VERIFIER_nondet_bool();
    _x_s0_x = __VERIFIER_nondet_float();
    _x_s0_evt0 = __VERIFIER_nondet_bool();
    _x_s0_evt1 = __VERIFIER_nondet_bool();
    _x_s0_evt2 = __VERIFIER_nondet_bool();
    _x_s1_l1 = __VERIFIER_nondet_bool();
    _x_s1_l0 = __VERIFIER_nondet_bool();
    _x_s1_x = __VERIFIER_nondet_float();
    _x_s1_evt0 = __VERIFIER_nondet_bool();
    _x_s1_evt1 = __VERIFIER_nondet_bool();
    _x_s1_evt2 = __VERIFIER_nondet_bool();

    __ok = ((((((((((((((((((((((((((((( !_x_s1_evt2) && (_x_s1_evt0 && ( !_x_s1_evt1))) || (((( !_x_s1_evt2) && (( !_x_s1_evt0) && ( !_x_s1_evt1))) || (_x_s1_evt2 && (( !_x_s1_evt0) && ( !_x_s1_evt1)))) || ((( !_x_s1_evt2) && (_x_s1_evt1 && ( !_x_s1_evt0))) || (_x_s1_evt2 && (_x_s1_evt1 && ( !_x_s1_evt0)))))) && ((( !_x_s1_l0) && ( !_x_s1_l1)) || ((_x_s1_l1 && ( !_x_s1_l0)) || (_x_s1_l0 && ( !_x_s1_l1))))) && ((_x_s1_x <= 404.0) || ( !(_x_s1_l1 && ( !_x_s1_l0))))) && ((_x_s1_x <= 26.0) || ( !(_x_s1_l0 && ( !_x_s1_l1))))) && ((delta <= 0.0) || (((s1_l0 == _x_s1_l0) && (s1_l1 == _x_s1_l1)) && ((delta + (s1_x + (-1.0 * _x_s1_x))) == 0.0)))) && ((((s1_l0 == _x_s1_l0) && (s1_l1 == _x_s1_l1)) && ((delta + (s1_x + (-1.0 * _x_s1_x))) == 0.0)) || ( !(( !s1_evt2) && (( !s1_evt0) && ( !s1_evt1)))))) && (((_x_s1_l0 && ( !_x_s1_l1)) || ((( !_x_s1_l0) && ( !_x_s1_l1)) || (_x_s1_l1 && ( !_x_s1_l0)))) || ( !((( !s1_l0) && ( !s1_l1)) && ((delta == 0.0) && ( !(( !s1_evt2) && (( !s1_evt0) && ( !s1_evt1))))))))) && (((( !s1_evt2) && (s1_evt0 && ( !s1_evt1))) && (_x_s1_x == 0.0)) || ( !((( !_x_s1_l0) && ( !_x_s1_l1)) && ((( !s1_l0) && ( !s1_l1)) && ((delta == 0.0) && ( !(( !s1_evt2) && (( !s1_evt0) && ( !s1_evt1)))))))))) && (((s1_evt2 && (( !s1_evt0) && ( !s1_evt1))) && (_x_s1_x == 0.0)) || ( !((_x_s1_l1 && ( !_x_s1_l0)) && ((( !s1_l0) && ( !s1_l1)) && ((delta == 0.0) && ( !(( !s1_evt2) && (( !s1_evt0) && ( !s1_evt1)))))))))) && (((_x_s1_x == 0.0) && ((s1_evt2 && (s1_evt1 && ( !s1_evt0))) || (( !s1_evt2) && (s1_evt0 && ( !s1_evt1))))) || ( !((_x_s1_l0 && ( !_x_s1_l1)) && ((( !s1_l0) && ( !s1_l1)) && ((delta == 0.0) && ( !(( !s1_evt2) && (( !s1_evt0) && ( !s1_evt1)))))))))) && (((( !_x_s1_l0) && ( !_x_s1_l1)) || (_x_s1_l0 && ( !_x_s1_l1))) || ( !((s1_l1 && ( !s1_l0)) && ((delta == 0.0) && ( !(( !s1_evt2) && (( !s1_evt0) && ( !s1_evt1))))))))) && (((404.0 <= s1_x) && ((( !s1_evt2) && (s1_evt1 && ( !s1_evt0))) && (_x_s1_x == 0.0))) || ( !((( !_x_s1_l0) && ( !_x_s1_l1)) && ((s1_l1 && ( !s1_l0)) && ((delta == 0.0) && ( !(( !s1_evt2) && (( !s1_evt0) && ( !s1_evt1)))))))))) && (((s1_x <= 26.0) && ((( !s1_evt2) && (s1_evt0 && ( !s1_evt1))) && (_x_s1_x == 0.0))) || ( !((_x_s1_l0 && ( !_x_s1_l1)) && ((s1_l1 && ( !s1_l0)) && ((delta == 0.0) && ( !(( !s1_evt2) && (( !s1_evt0) && ( !s1_evt1)))))))))) && (((_x_s1_l1 && ( !_x_s1_l0)) || (_x_s1_l0 && ( !_x_s1_l1))) || ( !((s1_l0 && ( !s1_l1)) && ((delta == 0.0) && ( !(( !s1_evt2) && (( !s1_evt0) && ( !s1_evt1))))))))) && (((s1_x <= 26.0) && ((( !s1_evt2) && (s1_evt0 && ( !s1_evt1))) && (_x_s1_x == 0.0))) || ( !((_x_s1_l0 && ( !_x_s1_l1)) && ((s1_l0 && ( !s1_l1)) && ((delta == 0.0) && ( !(( !s1_evt2) && (( !s1_evt0) && ( !s1_evt1)))))))))) && (((s1_x <= 26.0) && ((s1_evt2 && (( !s1_evt0) && ( !s1_evt1))) && (_x_s1_x == 0.0))) || ( !((_x_s1_l1 && ( !_x_s1_l0)) && ((s1_l0 && ( !s1_l1)) && ((delta == 0.0) && ( !(( !s1_evt2) && (( !s1_evt0) && ( !s1_evt1)))))))))) && ((((((((((((((((((( !_x_s0_evt2) && (_x_s0_evt0 && ( !_x_s0_evt1))) || (((( !_x_s0_evt2) && (( !_x_s0_evt0) && ( !_x_s0_evt1))) || (_x_s0_evt2 && (( !_x_s0_evt0) && ( !_x_s0_evt1)))) || ((( !_x_s0_evt2) && (_x_s0_evt1 && ( !_x_s0_evt0))) || (_x_s0_evt2 && (_x_s0_evt1 && ( !_x_s0_evt0)))))) && ((( !_x_s0_l0) && ( !_x_s0_l1)) || ((_x_s0_l1 && ( !_x_s0_l0)) || (_x_s0_l0 && ( !_x_s0_l1))))) && ((_x_s0_x <= 404.0) || ( !(_x_s0_l1 && ( !_x_s0_l0))))) && ((_x_s0_x <= 26.0) || ( !(_x_s0_l0 && ( !_x_s0_l1))))) && ((delta <= 0.0) || (((s0_l0 == _x_s0_l0) && (s0_l1 == _x_s0_l1)) && ((delta + (s0_x + (-1.0 * _x_s0_x))) == 0.0)))) && ((((s0_l0 == _x_s0_l0) && (s0_l1 == _x_s0_l1)) && ((delta + (s0_x + (-1.0 * _x_s0_x))) == 0.0)) || ( !(( !s0_evt2) && (( !s0_evt0) && ( !s0_evt1)))))) && (((_x_s0_l0 && ( !_x_s0_l1)) || ((( !_x_s0_l0) && ( !_x_s0_l1)) || (_x_s0_l1 && ( !_x_s0_l0)))) || ( !((( !s0_l0) && ( !s0_l1)) && ((delta == 0.0) && ( !(( !s0_evt2) && (( !s0_evt0) && ( !s0_evt1))))))))) && (((( !s0_evt2) && (s0_evt0 && ( !s0_evt1))) && (_x_s0_x == 0.0)) || ( !((( !_x_s0_l0) && ( !_x_s0_l1)) && ((( !s0_l0) && ( !s0_l1)) && ((delta == 0.0) && ( !(( !s0_evt2) && (( !s0_evt0) && ( !s0_evt1)))))))))) && (((s0_evt2 && (( !s0_evt0) && ( !s0_evt1))) && (_x_s0_x == 0.0)) || ( !((_x_s0_l1 && ( !_x_s0_l0)) && ((( !s0_l0) && ( !s0_l1)) && ((delta == 0.0) && ( !(( !s0_evt2) && (( !s0_evt0) && ( !s0_evt1)))))))))) && (((_x_s0_x == 0.0) && ((s0_evt2 && (s0_evt1 && ( !s0_evt0))) || (( !s0_evt2) && (s0_evt0 && ( !s0_evt1))))) || ( !((_x_s0_l0 && ( !_x_s0_l1)) && ((( !s0_l0) && ( !s0_l1)) && ((delta == 0.0) && ( !(( !s0_evt2) && (( !s0_evt0) && ( !s0_evt1)))))))))) && (((( !_x_s0_l0) && ( !_x_s0_l1)) || (_x_s0_l0 && ( !_x_s0_l1))) || ( !((s0_l1 && ( !s0_l0)) && ((delta == 0.0) && ( !(( !s0_evt2) && (( !s0_evt0) && ( !s0_evt1))))))))) && (((404.0 <= s0_x) && ((( !s0_evt2) && (s0_evt1 && ( !s0_evt0))) && (_x_s0_x == 0.0))) || ( !((( !_x_s0_l0) && ( !_x_s0_l1)) && ((s0_l1 && ( !s0_l0)) && ((delta == 0.0) && ( !(( !s0_evt2) && (( !s0_evt0) && ( !s0_evt1)))))))))) && (((s0_x <= 26.0) && ((( !s0_evt2) && (s0_evt0 && ( !s0_evt1))) && (_x_s0_x == 0.0))) || ( !((_x_s0_l0 && ( !_x_s0_l1)) && ((s0_l1 && ( !s0_l0)) && ((delta == 0.0) && ( !(( !s0_evt2) && (( !s0_evt0) && ( !s0_evt1)))))))))) && (((_x_s0_l1 && ( !_x_s0_l0)) || (_x_s0_l0 && ( !_x_s0_l1))) || ( !((s0_l0 && ( !s0_l1)) && ((delta == 0.0) && ( !(( !s0_evt2) && (( !s0_evt0) && ( !s0_evt1))))))))) && (((s0_x <= 26.0) && ((( !s0_evt2) && (s0_evt0 && ( !s0_evt1))) && (_x_s0_x == 0.0))) || ( !((_x_s0_l0 && ( !_x_s0_l1)) && ((s0_l0 && ( !s0_l1)) && ((delta == 0.0) && ( !(( !s0_evt2) && (( !s0_evt0) && ( !s0_evt1)))))))))) && (((s0_x <= 26.0) && ((s0_evt2 && (( !s0_evt0) && ( !s0_evt1))) && (_x_s0_x == 0.0))) || ( !((_x_s0_l1 && ( !_x_s0_l0)) && ((s0_l0 && ( !s0_l1)) && ((delta == 0.0) && ( !(( !s0_evt2) && (( !s0_evt0) && ( !s0_evt1)))))))))) && (((((((((((((((( !_x_bus_evt2) && (( !_x_bus_evt0) && ( !_x_bus_evt1))) || (((_x_bus_evt2 && (( !_x_bus_evt0) && ( !_x_bus_evt1))) || (( !_x_bus_evt2) && (_x_bus_evt1 && ( !_x_bus_evt0)))) || ((_x_bus_evt2 && (_x_bus_evt1 && ( !_x_bus_evt0))) || (( !_x_bus_evt2) && (_x_bus_evt0 && ( !_x_bus_evt1)))))) && (((( !_x_bus_l0) && ( !_x_bus_l1)) || (_x_bus_l1 && ( !_x_bus_l0))) || ((_x_bus_l0 && ( !_x_bus_l1)) || (_x_bus_l0 && _x_bus_l1)))) && ((( !(13.0 <= _x_bus_x)) || ( !(_x_bus_l0 && ( !_x_bus_l1)))) && ((_x_delta == 0.0) || ( !(_x_bus_l0 && _x_bus_l1))))) && ((delta <= 0.0) || (((delta + (bus_x + (-1.0 * _x_bus_x))) == 0.0) && (((bus_l0 == _x_bus_l0) && (bus_l1 == _x_bus_l1)) && (bus_j == _x_bus_j))))) && ((((delta + (bus_x + (-1.0 * _x_bus_x))) == 0.0) && (((bus_l0 == _x_bus_l0) && (bus_l1 == _x_bus_l1)) && (bus_j == _x_bus_j))) || ( !(( !bus_evt2) && (( !bus_evt0) && ( !bus_evt1)))))) && ((((bus_evt2 && (( !bus_evt0) && ( !bus_evt1))) && (_x_bus_l1 && ( !_x_bus_l0))) && ((bus_j == _x_bus_j) && (_x_bus_x == 0.0))) || ( !((( !bus_l0) && ( !bus_l1)) && ((delta == 0.0) && ( !(( !bus_evt2) && (( !bus_evt0) && ( !bus_evt1))))))))) && (((bus_j == _x_bus_j) && ((_x_bus_l0 && ( !_x_bus_l1)) || ((( !_x_bus_l0) && ( !_x_bus_l1)) || (_x_bus_l1 && ( !_x_bus_l0))))) || ( !((bus_l1 && ( !bus_l0)) && ((delta == 0.0) && ( !(( !bus_evt2) && (( !bus_evt0) && ( !bus_evt1))))))))) && (((( !bus_evt2) && (bus_evt1 && ( !bus_evt0))) && (_x_bus_x == 0.0)) || ( !(((delta == 0.0) && ( !(( !bus_evt2) && (( !bus_evt0) && ( !bus_evt1))))) && ((( !_x_bus_l0) && ( !_x_bus_l1)) && (bus_l1 && ( !bus_l0))))))) && (((bus_evt2 && (bus_evt1 && ( !bus_evt0))) && ((13.0 <= bus_x) && (bus_x == _x_bus_x))) || ( !(((delta == 0.0) && ( !(( !bus_evt2) && (( !bus_evt0) && ( !bus_evt1))))) && ((bus_l1 && ( !bus_l0)) && (_x_bus_l1 && ( !_x_bus_l0))))))) && (((bus_evt2 && (( !bus_evt0) && ( !bus_evt1))) && (( !(13.0 <= bus_x)) && (_x_bus_x == 0.0))) || ( !(((delta == 0.0) && ( !(( !bus_evt2) && (( !bus_evt0) && ( !bus_evt1))))) && ((bus_l1 && ( !bus_l0)) && (_x_bus_l0 && ( !_x_bus_l1))))))) && (((((_x_bus_l0 && _x_bus_l1) && ( !(13.0 <= bus_x))) && ((( !bus_evt2) && (bus_evt0 && ( !bus_evt1))) && (bus_cd_id == bus_j))) && ((_x_bus_x == 0.0) && ((bus_j + (-1 * _x_bus_j)) == -1))) || ( !((bus_l0 && ( !bus_l1)) && ((delta == 0.0) && ( !(( !bus_evt2) && (( !bus_evt0) && ( !bus_evt1))))))))) && ((((bus_j + (-1 * _x_bus_j)) == -1) && (((( !bus_evt2) && (bus_evt0 && ( !bus_evt1))) && (bus_cd_id == bus_j)) && ((_x_bus_x == 0.0) && ( !(1 <= bus_j))))) || ( !(((delta == 0.0) && ( !(( !bus_evt2) && (( !bus_evt0) && ( !bus_evt1))))) && ((bus_l0 && bus_l1) && (_x_bus_l0 && _x_bus_l1)))))) && (((((( !bus_evt2) && (bus_evt0 && ( !bus_evt1))) && (bus_j == 1)) && ((_x_bus_x == 0.0) && (bus_cd_id == bus_j))) && (_x_bus_j == 0)) || ( !(((delta == 0.0) && ( !(( !bus_evt2) && (( !bus_evt0) && ( !bus_evt1))))) && ((( !_x_bus_l0) && ( !_x_bus_l1)) && (bus_l0 && bus_l1)))))) && (0.0 <= _x_delta)))) && (((( !s0_evt2) && (( !s0_evt0) && ( !s0_evt1))) || (( !s1_evt2) && (( !s1_evt0) && ( !s1_evt1)))) || ( !(delta == 0.0)))) && (( !(delta == 0.0)) || (( !(( !s1_evt2) && (( !s1_evt0) && ( !s1_evt1)))) || (( !(( !bus_evt2) && (( !bus_evt0) && ( !bus_evt1)))) || ( !(( !s0_evt2) && (( !s0_evt0) && ( !s0_evt1)))))))) && (( !(delta == 0.0)) || ((bus_evt2 && (( !bus_evt0) && ( !bus_evt1))) == ((s0_evt2 && (( !s0_evt0) && ( !s0_evt1))) || (s1_evt2 && (( !s1_evt0) && ( !s1_evt1))))))) && (( !(delta == 0.0)) || ((( !bus_evt2) && (bus_evt1 && ( !bus_evt0))) == ((( !s0_evt2) && (s0_evt1 && ( !s0_evt0))) || (( !s1_evt2) && (s1_evt1 && ( !s1_evt0))))))) && (( !(delta == 0.0)) || ((bus_evt2 && (bus_evt1 && ( !bus_evt0))) == ((s0_evt2 && (s0_evt1 && ( !s0_evt0))) || (s1_evt2 && (s1_evt1 && ( !s1_evt0))))))) && (( !(delta == 0.0)) || ((( !bus_evt2) && (bus_evt0 && ( !bus_evt1))) == ((( !s0_evt2) && (s0_evt0 && ( !s0_evt1))) || (( !s1_evt2) && (s1_evt0 && ( !s1_evt1))))))) && (( !(delta == 0.0)) || ((( !s0_evt2) && (s0_evt0 && ( !s0_evt1))) == ((( !bus_evt2) && (bus_evt0 && ( !bus_evt1))) && (bus_cd_id == 0))))) && (( !(delta == 0.0)) || ((( !s1_evt2) && (s1_evt0 && ( !s1_evt1))) == ((( !bus_evt2) && (bus_evt0 && ( !bus_evt1))) && (bus_cd_id == 1))))) && (((delta == _x__diverge_delta) || ( !(1.0 <= _diverge_delta))) && ((1.0 <= _diverge_delta) || ((delta + (_diverge_delta + (-1.0 * _x__diverge_delta))) == 0.0)))) && ((((((_EL_U_557 == (_x__EL_U_557 || ( !(_x__EL_U_555 || (1.0 <= _x__diverge_delta))))) && ((_EL_U_555 == (_x__EL_U_555 || (1.0 <= _x__diverge_delta))) && ((_EL_U_559 == ((( !_x_s0_l0) && ( !_x_s0_l1)) || _x__EL_U_559)) && (_EL_U_562 == (_x__EL_U_562 || ( !(( !(_x_s0_l1 && ( !_x_s0_l0))) || ((( !_x_s0_l0) && ( !_x_s0_l1)) || _x__EL_U_559)))))))) && (_x__J582 == (( !(((_J582 && _J591) && _J597) && _J603)) && ((((_J582 && _J591) && _J597) && _J603) || (((( !s0_l0) && ( !s0_l1)) || ( !((( !s0_l0) && ( !s0_l1)) || _EL_U_559))) || _J582))))) && (_x__J591 == (( !(((_J582 && _J591) && _J597) && _J603)) && ((((_J582 && _J591) && _J597) && _J603) || ((( !(( !(s0_l1 && ( !s0_l0))) || ((( !s0_l0) && ( !s0_l1)) || _EL_U_559))) || ( !(_EL_U_562 || ( !(( !(s0_l1 && ( !s0_l0))) || ((( !s0_l0) && ( !s0_l1)) || _EL_U_559)))))) || _J591))))) && (_x__J597 == (( !(((_J582 && _J591) && _J597) && _J603)) && ((((_J582 && _J591) && _J597) && _J603) || (((1.0 <= _diverge_delta) || ( !((1.0 <= _diverge_delta) || _EL_U_555))) || _J597))))) && (_x__J603 == (( !(((_J582 && _J591) && _J597) && _J603)) && ((((_J582 && _J591) && _J597) && _J603) || ((( !((1.0 <= _diverge_delta) || _EL_U_555)) || ( !(_EL_U_557 || ( !((1.0 <= _diverge_delta) || _EL_U_555))))) || _J603))))));
    _diverge_delta = _x__diverge_delta;
    delta = _x_delta;
    bus_l1 = _x_bus_l1;
    bus_l0 = _x_bus_l0;
    _J603 = _x__J603;
    bus_x = _x_bus_x;
    _J597 = _x__J597;
    _J591 = _x__J591;
    _J582 = _x__J582;
    _EL_U_555 = _x__EL_U_555;
    bus_j = _x_bus_j;
    _EL_U_557 = _x__EL_U_557;
    _EL_U_559 = _x__EL_U_559;
    bus_evt1 = _x_bus_evt1;
    bus_evt0 = _x_bus_evt0;
    _EL_U_562 = _x__EL_U_562;
    bus_evt2 = _x_bus_evt2;
    s0_l1 = _x_s0_l1;
    bus_cd_id = _x_bus_cd_id;
    s0_l0 = _x_s0_l0;
    s0_x = _x_s0_x;
    s0_evt0 = _x_s0_evt0;
    s0_evt1 = _x_s0_evt1;
    s0_evt2 = _x_s0_evt2;
    s1_l1 = _x_s1_l1;
    s1_l0 = _x_s1_l0;
    s1_x = _x_s1_x;
    s1_evt0 = _x_s1_evt0;
    s1_evt1 = _x_s1_evt1;
    s1_evt2 = _x_s1_evt2;

  }
}
