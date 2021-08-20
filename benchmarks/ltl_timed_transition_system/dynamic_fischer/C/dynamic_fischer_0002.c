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
float max_prop, _x_max_prop;
float proposed1, _x_proposed1;
float proposed0, _x_proposed0;
bool turn0, _x_turn0;
bool inc_max_prop, _x_inc_max_prop;
bool id1, _x_id1;
bool id0, _x_id0;
bool p0_l0, _x_p0_l0;
bool p0_l1, _x_p0_l1;
float p0_x, _x_p0_x;
float p0_saved_max, _x_p0_saved_max;
bool p1_l0, _x_p1_l0;
bool p1_l1, _x_p1_l1;
float p1_x, _x_p1_x;
float p1_saved_max, _x_p1_saved_max;
bool _J352, _x__J352;
bool _J346, _x__J346;
bool _J340, _x__J340;
bool _J334, _x__J334;
bool _EL_U_307, _x__EL_U_307;
bool _EL_U_309, _x__EL_U_309;
bool _EL_U_312, _x__EL_U_312;
bool _EL_U_314, _x__EL_U_314;

  int __steps_to_fair = __VERIFIER_nondet_int();
  _diverge_delta = __VERIFIER_nondet_float();
  delta = __VERIFIER_nondet_float();
  max_prop = __VERIFIER_nondet_float();
  proposed1 = __VERIFIER_nondet_float();
  proposed0 = __VERIFIER_nondet_float();
  turn0 = __VERIFIER_nondet_bool();
  inc_max_prop = __VERIFIER_nondet_bool();
  id1 = __VERIFIER_nondet_bool();
  id0 = __VERIFIER_nondet_bool();
  p0_l0 = __VERIFIER_nondet_bool();
  p0_l1 = __VERIFIER_nondet_bool();
  p0_x = __VERIFIER_nondet_float();
  p0_saved_max = __VERIFIER_nondet_float();
  p1_l0 = __VERIFIER_nondet_bool();
  p1_l1 = __VERIFIER_nondet_bool();
  p1_x = __VERIFIER_nondet_float();
  p1_saved_max = __VERIFIER_nondet_float();
  _J352 = __VERIFIER_nondet_bool();
  _J346 = __VERIFIER_nondet_bool();
  _J340 = __VERIFIER_nondet_bool();
  _J334 = __VERIFIER_nondet_bool();
  _EL_U_307 = __VERIFIER_nondet_bool();
  _EL_U_309 = __VERIFIER_nondet_bool();
  _EL_U_312 = __VERIFIER_nondet_bool();
  _EL_U_314 = __VERIFIER_nondet_bool();

  bool __ok = ((((((((( !p1_l0) && ( !p1_l1)) && (((( !p1_l0) && ( !p1_l1)) || (p1_l0 && ( !p1_l1))) || ((p1_l1 && ( !p1_l0)) || (p1_l0 && p1_l1)))) && ((p1_x == 0.0) && (max_prop == p1_saved_max))) && ( !(proposed1 <= 0.0))) && ((p1_x <= proposed1) || ( !(p1_l1 && ( !p1_l0))))) && ((((((( !p0_l0) && ( !p0_l1)) && (((( !p0_l0) && ( !p0_l1)) || (p0_l0 && ( !p0_l1))) || ((p0_l1 && ( !p0_l0)) || (p0_l0 && p0_l1)))) && ((p0_x == 0.0) && (max_prop == p0_saved_max))) && ( !(proposed0 <= 0.0))) && ((p0_x <= proposed0) || ( !(p0_l1 && ( !p0_l0))))) && (((((((id1 && ( !id0)) || ((( !id0) && ( !id1)) || (id0 && ( !id1)))) && ((( !id0) && ( !id1)) && inc_max_prop)) && (0.0 <= delta)) && (proposed0 <= max_prop)) && (proposed1 <= max_prop)) && ((proposed0 == max_prop) || (proposed1 == max_prop))))) && (delta == _diverge_delta)) && ((((( !((_EL_U_314 || ( !(( !inc_max_prop) || _EL_U_312))) || (_EL_U_309 || ( !((1.0 <= _diverge_delta) || _EL_U_307))))) && ( !_J334)) && ( !_J340)) && ( !_J346)) && ( !_J352)));
  while (__steps_to_fair >= 0 && __ok) {
    if ((((_J334 && _J340) && _J346) && _J352)) {
      __steps_to_fair = __VERIFIER_nondet_int();
    } else {
      __steps_to_fair--;
    }
    _x__diverge_delta = __VERIFIER_nondet_float();
    _x_delta = __VERIFIER_nondet_float();
    _x_max_prop = __VERIFIER_nondet_float();
    _x_proposed1 = __VERIFIER_nondet_float();
    _x_proposed0 = __VERIFIER_nondet_float();
    _x_turn0 = __VERIFIER_nondet_bool();
    _x_inc_max_prop = __VERIFIER_nondet_bool();
    _x_id1 = __VERIFIER_nondet_bool();
    _x_id0 = __VERIFIER_nondet_bool();
    _x_p0_l0 = __VERIFIER_nondet_bool();
    _x_p0_l1 = __VERIFIER_nondet_bool();
    _x_p0_x = __VERIFIER_nondet_float();
    _x_p0_saved_max = __VERIFIER_nondet_float();
    _x_p1_l0 = __VERIFIER_nondet_bool();
    _x_p1_l1 = __VERIFIER_nondet_bool();
    _x_p1_x = __VERIFIER_nondet_float();
    _x_p1_saved_max = __VERIFIER_nondet_float();
    _x__J352 = __VERIFIER_nondet_bool();
    _x__J346 = __VERIFIER_nondet_bool();
    _x__J340 = __VERIFIER_nondet_bool();
    _x__J334 = __VERIFIER_nondet_bool();
    _x__EL_U_307 = __VERIFIER_nondet_bool();
    _x__EL_U_309 = __VERIFIER_nondet_bool();
    _x__EL_U_312 = __VERIFIER_nondet_bool();
    _x__EL_U_314 = __VERIFIER_nondet_bool();

    __ok = (((((((((((((( !_x_p1_l0) && ( !_x_p1_l1)) || (_x_p1_l0 && ( !_x_p1_l1))) || ((_x_p1_l1 && ( !_x_p1_l0)) || (_x_p1_l0 && _x_p1_l1))) && ( !(_x_proposed1 <= 0.0))) && ((_x_p1_x <= _x_proposed1) || ( !(_x_p1_l1 && ( !_x_p1_l0))))) && (((((p1_l0 == _x_p1_l0) && (p1_l1 == _x_p1_l1)) && ((delta + (p1_x + (-1.0 * _x_p1_x))) == 0.0)) && ((p1_saved_max == _x_p1_saved_max) && (proposed1 == _x_proposed1))) || ( !(( !turn0) || ( !(delta <= 0.0)))))) && (((((_x_p1_l1 && ( !_x_p1_l0)) && (_x_p1_x == 0.0)) && (((id0 == _x_id0) && (id1 == _x_id1)) && (proposed1 == _x_proposed1))) && (max_prop == _x_p1_saved_max)) || ( !((( !p1_l0) && ( !p1_l1)) && (turn0 && (delta == 0.0)))))) && (((max_prop == _x_p1_saved_max) && (((_x_p1_l0 && ( !_x_p1_l1)) && (_x_p1_x == 0.0)) && ((_x_id0 && ( !_x_id1)) && (proposed1 == _x_proposed1)))) || ( !((p1_l1 && ( !p1_l0)) && (turn0 && (delta == 0.0)))))) && (((((id0 == _x_id0) && (id1 == _x_id1)) && (proposed1 == _x_proposed1)) && ((max_prop == _x_p1_saved_max) && (((( !_x_p1_l0) && ( !_x_p1_l1)) && (_x_p1_x == 0.0)) || ((_x_p1_l0 && _x_p1_l1) && (p1_x == _x_p1_x))))) || ( !((p1_l0 && ( !p1_l1)) && (turn0 && (delta == 0.0)))))) && (((max_prop == _x_p1_saved_max) && (((( !_x_p1_l0) && ( !_x_p1_l1)) && (p1_x == _x_p1_x)) && ((_x_id1 && ( !_x_id0)) && ( !(proposed1 <= _x_proposed1))))) || ( !((p1_l0 && p1_l1) && (turn0 && (delta == 0.0)))))) && (((((((((((( !_x_p0_l0) && ( !_x_p0_l1)) || (_x_p0_l0 && ( !_x_p0_l1))) || ((_x_p0_l1 && ( !_x_p0_l0)) || (_x_p0_l0 && _x_p0_l1))) && ( !(_x_proposed0 <= 0.0))) && ((_x_p0_x <= _x_proposed0) || ( !(_x_p0_l1 && ( !_x_p0_l0))))) && (((((p0_l0 == _x_p0_l0) && (p0_l1 == _x_p0_l1)) && ((delta + (p0_x + (-1.0 * _x_p0_x))) == 0.0)) && ((p0_saved_max == _x_p0_saved_max) && (proposed0 == _x_proposed0))) || ( !(turn0 || ( !(delta <= 0.0)))))) && (((((_x_p0_l1 && ( !_x_p0_l0)) && (_x_p0_x == 0.0)) && (((id0 == _x_id0) && (id1 == _x_id1)) && (proposed0 == _x_proposed0))) && (max_prop == _x_p0_saved_max)) || ( !((( !p0_l0) && ( !p0_l1)) && (( !turn0) && (delta == 0.0)))))) && (((max_prop == _x_p0_saved_max) && (((_x_p0_l0 && ( !_x_p0_l1)) && (_x_p0_x == 0.0)) && ((( !_x_id0) && ( !_x_id1)) && (proposed0 == _x_proposed0)))) || ( !((p0_l1 && ( !p0_l0)) && (( !turn0) && (delta == 0.0)))))) && (((((id0 == _x_id0) && (id1 == _x_id1)) && (proposed0 == _x_proposed0)) && ((max_prop == _x_p0_saved_max) && (((( !_x_p0_l0) && ( !_x_p0_l1)) && (_x_p0_x == 0.0)) || ((_x_p0_l0 && _x_p0_l1) && (p0_x == _x_p0_x))))) || ( !((p0_l0 && ( !p0_l1)) && (( !turn0) && (delta == 0.0)))))) && (((max_prop == _x_p0_saved_max) && (((( !_x_p0_l0) && ( !_x_p0_l1)) && (p0_x == _x_p0_x)) && ((_x_id1 && ( !_x_id0)) && ( !(proposed0 <= _x_proposed0))))) || ( !((p0_l0 && p0_l1) && (( !turn0) && (delta == 0.0)))))) && ((((((((_x_id1 && ( !_x_id0)) || ((( !_x_id0) && ( !_x_id1)) || (_x_id0 && ( !_x_id1)))) && ((delta <= 0.0) || (((id0 == _x_id0) && (id1 == _x_id1)) && (turn0 == _x_turn0)))) && (0.0 <= _x_delta)) && (_x_proposed0 <= _x_max_prop)) && (_x_proposed1 <= _x_max_prop)) && ((_x_proposed0 == _x_max_prop) || (_x_proposed1 == _x_max_prop))) && (_x_inc_max_prop == (max_prop <= _x_max_prop))))) && (((delta == _x__diverge_delta) || ( !(1.0 <= _diverge_delta))) && ((1.0 <= _diverge_delta) || ((delta + (_diverge_delta + (-1.0 * _x__diverge_delta))) == 0.0)))) && ((((((_EL_U_309 == (_x__EL_U_309 || ( !(_x__EL_U_307 || (1.0 <= _x__diverge_delta))))) && ((_EL_U_307 == (_x__EL_U_307 || (1.0 <= _x__diverge_delta))) && ((_EL_U_312 == (_x__EL_U_312 || ( !_x_inc_max_prop))) && (_EL_U_314 == (_x__EL_U_314 || ( !(_x__EL_U_312 || ( !_x_inc_max_prop)))))))) && (_x__J334 == (( !(((_J334 && _J340) && _J346) && _J352)) && ((((_J334 && _J340) && _J346) && _J352) || ((( !inc_max_prop) || ( !(( !inc_max_prop) || _EL_U_312))) || _J334))))) && (_x__J340 == (( !(((_J334 && _J340) && _J346) && _J352)) && ((((_J334 && _J340) && _J346) && _J352) || ((( !(( !inc_max_prop) || _EL_U_312)) || ( !(_EL_U_314 || ( !(( !inc_max_prop) || _EL_U_312))))) || _J340))))) && (_x__J346 == (( !(((_J334 && _J340) && _J346) && _J352)) && ((((_J334 && _J340) && _J346) && _J352) || (((1.0 <= _diverge_delta) || ( !((1.0 <= _diverge_delta) || _EL_U_307))) || _J346))))) && (_x__J352 == (( !(((_J334 && _J340) && _J346) && _J352)) && ((((_J334 && _J340) && _J346) && _J352) || ((( !((1.0 <= _diverge_delta) || _EL_U_307)) || ( !(_EL_U_309 || ( !((1.0 <= _diverge_delta) || _EL_U_307))))) || _J352))))));
    _diverge_delta = _x__diverge_delta;
    delta = _x_delta;
    max_prop = _x_max_prop;
    proposed1 = _x_proposed1;
    proposed0 = _x_proposed0;
    turn0 = _x_turn0;
    inc_max_prop = _x_inc_max_prop;
    id1 = _x_id1;
    id0 = _x_id0;
    p0_l0 = _x_p0_l0;
    p0_l1 = _x_p0_l1;
    p0_x = _x_p0_x;
    p0_saved_max = _x_p0_saved_max;
    p1_l0 = _x_p1_l0;
    p1_l1 = _x_p1_l1;
    p1_x = _x_p1_x;
    p1_saved_max = _x_p1_saved_max;
    _J352 = _x__J352;
    _J346 = _x__J346;
    _J340 = _x__J340;
    _J334 = _x__J334;
    _EL_U_307 = _x__EL_U_307;
    _EL_U_309 = _x__EL_U_309;
    _EL_U_312 = _x__EL_U_312;
    _EL_U_314 = _x__EL_U_314;

  }
}
