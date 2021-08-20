extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);
typedef enum {false, true} bool;
bool __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}

int main()
{
bool _J491, _x__J491;
float _diverge_delta, _x__diverge_delta;
float delta, _x_delta;
bool _J485, _x__J485;
float max_prop, _x_max_prop;
float proposed2, _x_proposed2;
bool _J479, _x__J479;
float proposed1, _x_proposed1;
bool _J473, _x__J473;
float proposed0, _x_proposed0;
bool _EL_U_446, _x__EL_U_446;
bool _EL_U_448, _x__EL_U_448;
bool _EL_U_451, _x__EL_U_451;
bool inc_max_prop, _x_inc_max_prop;
bool id1, _x_id1;
bool _EL_U_453, _x__EL_U_453;
bool id0, _x_id0;
bool turn1, _x_turn1;
bool turn0, _x_turn0;
bool p0_l0, _x_p0_l0;
bool p0_l1, _x_p0_l1;
float p0_x, _x_p0_x;
float p0_saved_max, _x_p0_saved_max;
bool p1_l0, _x_p1_l0;
bool p1_l1, _x_p1_l1;
float p1_x, _x_p1_x;
float p1_saved_max, _x_p1_saved_max;
bool p2_l0, _x_p2_l0;
bool p2_l1, _x_p2_l1;
float p2_x, _x_p2_x;
float p2_saved_max, _x_p2_saved_max;

  int __steps_to_fair = __VERIFIER_nondet_int();
  _J491 = __VERIFIER_nondet_bool();
  _diverge_delta = __VERIFIER_nondet_float();
  delta = __VERIFIER_nondet_float();
  _J485 = __VERIFIER_nondet_bool();
  max_prop = __VERIFIER_nondet_float();
  proposed2 = __VERIFIER_nondet_float();
  _J479 = __VERIFIER_nondet_bool();
  proposed1 = __VERIFIER_nondet_float();
  _J473 = __VERIFIER_nondet_bool();
  proposed0 = __VERIFIER_nondet_float();
  _EL_U_446 = __VERIFIER_nondet_bool();
  _EL_U_448 = __VERIFIER_nondet_bool();
  _EL_U_451 = __VERIFIER_nondet_bool();
  inc_max_prop = __VERIFIER_nondet_bool();
  id1 = __VERIFIER_nondet_bool();
  _EL_U_453 = __VERIFIER_nondet_bool();
  id0 = __VERIFIER_nondet_bool();
  turn1 = __VERIFIER_nondet_bool();
  turn0 = __VERIFIER_nondet_bool();
  p0_l0 = __VERIFIER_nondet_bool();
  p0_l1 = __VERIFIER_nondet_bool();
  p0_x = __VERIFIER_nondet_float();
  p0_saved_max = __VERIFIER_nondet_float();
  p1_l0 = __VERIFIER_nondet_bool();
  p1_l1 = __VERIFIER_nondet_bool();
  p1_x = __VERIFIER_nondet_float();
  p1_saved_max = __VERIFIER_nondet_float();
  p2_l0 = __VERIFIER_nondet_bool();
  p2_l1 = __VERIFIER_nondet_bool();
  p2_x = __VERIFIER_nondet_float();
  p2_saved_max = __VERIFIER_nondet_float();

  bool __ok = ((((((((( !p2_l0) && ( !p2_l1)) && (((( !p2_l0) && ( !p2_l1)) || (p2_l0 && ( !p2_l1))) || ((p2_l1 && ( !p2_l0)) || (p2_l0 && p2_l1)))) && ((p2_x == 0.0) && (max_prop == p2_saved_max))) && ( !(proposed2 <= 0.0))) && ((p2_x <= proposed2) || ( !(p2_l1 && ( !p2_l0))))) && ((((((( !p1_l0) && ( !p1_l1)) && (((( !p1_l0) && ( !p1_l1)) || (p1_l0 && ( !p1_l1))) || ((p1_l1 && ( !p1_l0)) || (p1_l0 && p1_l1)))) && ((p1_x == 0.0) && (max_prop == p1_saved_max))) && ( !(proposed1 <= 0.0))) && ((p1_x <= proposed1) || ( !(p1_l1 && ( !p1_l0))))) && ((((((( !p0_l0) && ( !p0_l1)) && (((( !p0_l0) && ( !p0_l1)) || (p0_l0 && ( !p0_l1))) || ((p0_l1 && ( !p0_l0)) || (p0_l0 && p0_l1)))) && ((p0_x == 0.0) && (max_prop == p0_saved_max))) && ( !(proposed0 <= 0.0))) && ((p0_x <= proposed0) || ( !(p0_l1 && ( !p0_l0))))) && (((((((((id0 && id1) || ((id1 && ( !id0)) || ((( !id0) && ( !id1)) || (id0 && ( !id1))))) && ((turn1 && ( !turn0)) || ((( !turn0) && ( !turn1)) || (turn0 && ( !turn1))))) && ((( !id0) && ( !id1)) && inc_max_prop)) && (0.0 <= delta)) && (proposed0 <= max_prop)) && (proposed1 <= max_prop)) && (proposed2 <= max_prop)) && (((proposed0 == max_prop) || (proposed1 == max_prop)) || (proposed2 == max_prop)))))) && (delta == _diverge_delta)) && ((((( !((_EL_U_453 || ( !(( !inc_max_prop) || _EL_U_451))) || (_EL_U_448 || ( !((1.0 <= _diverge_delta) || _EL_U_446))))) && ( !_J473)) && ( !_J479)) && ( !_J485)) && ( !_J491)));
  while (__steps_to_fair >= 0 && __ok) {
    if ((((_J473 && _J479) && _J485) && _J491)) {
      __steps_to_fair = __VERIFIER_nondet_int();
    } else {
      __steps_to_fair--;
    }
    _x__J491 = __VERIFIER_nondet_bool();
    _x__diverge_delta = __VERIFIER_nondet_float();
    _x_delta = __VERIFIER_nondet_float();
    _x__J485 = __VERIFIER_nondet_bool();
    _x_max_prop = __VERIFIER_nondet_float();
    _x_proposed2 = __VERIFIER_nondet_float();
    _x__J479 = __VERIFIER_nondet_bool();
    _x_proposed1 = __VERIFIER_nondet_float();
    _x__J473 = __VERIFIER_nondet_bool();
    _x_proposed0 = __VERIFIER_nondet_float();
    _x__EL_U_446 = __VERIFIER_nondet_bool();
    _x__EL_U_448 = __VERIFIER_nondet_bool();
    _x__EL_U_451 = __VERIFIER_nondet_bool();
    _x_inc_max_prop = __VERIFIER_nondet_bool();
    _x_id1 = __VERIFIER_nondet_bool();
    _x__EL_U_453 = __VERIFIER_nondet_bool();
    _x_id0 = __VERIFIER_nondet_bool();
    _x_turn1 = __VERIFIER_nondet_bool();
    _x_turn0 = __VERIFIER_nondet_bool();
    _x_p0_l0 = __VERIFIER_nondet_bool();
    _x_p0_l1 = __VERIFIER_nondet_bool();
    _x_p0_x = __VERIFIER_nondet_float();
    _x_p0_saved_max = __VERIFIER_nondet_float();
    _x_p1_l0 = __VERIFIER_nondet_bool();
    _x_p1_l1 = __VERIFIER_nondet_bool();
    _x_p1_x = __VERIFIER_nondet_float();
    _x_p1_saved_max = __VERIFIER_nondet_float();
    _x_p2_l0 = __VERIFIER_nondet_bool();
    _x_p2_l1 = __VERIFIER_nondet_bool();
    _x_p2_x = __VERIFIER_nondet_float();
    _x_p2_saved_max = __VERIFIER_nondet_float();

    __ok = (((((((((((((( !_x_p2_l0) && ( !_x_p2_l1)) || (_x_p2_l0 && ( !_x_p2_l1))) || ((_x_p2_l1 && ( !_x_p2_l0)) || (_x_p2_l0 && _x_p2_l1))) && ( !(_x_proposed2 <= 0.0))) && ((_x_p2_x <= _x_proposed2) || ( !(_x_p2_l1 && ( !_x_p2_l0))))) && (((((p2_l0 == _x_p2_l0) && (p2_l1 == _x_p2_l1)) && ((delta + (p2_x + (-1.0 * _x_p2_x))) == 0.0)) && ((p2_saved_max == _x_p2_saved_max) && (proposed2 == _x_proposed2))) || ( !(( !(delta <= 0.0)) || ( !(turn1 && ( !turn0))))))) && (((((_x_p2_l1 && ( !_x_p2_l0)) && (_x_p2_x == 0.0)) && (((id0 == _x_id0) && (id1 == _x_id1)) && (proposed2 == _x_proposed2))) && (max_prop == _x_p2_saved_max)) || ( !((( !p2_l0) && ( !p2_l1)) && ((turn1 && ( !turn0)) && (delta == 0.0)))))) && (((max_prop == _x_p2_saved_max) && (((_x_p2_l0 && ( !_x_p2_l1)) && (_x_p2_x == 0.0)) && ((_x_id1 && ( !_x_id0)) && (proposed2 == _x_proposed2)))) || ( !((p2_l1 && ( !p2_l0)) && ((turn1 && ( !turn0)) && (delta == 0.0)))))) && (((((id0 == _x_id0) && (id1 == _x_id1)) && (proposed2 == _x_proposed2)) && ((max_prop == _x_p2_saved_max) && (((( !_x_p2_l0) && ( !_x_p2_l1)) && (_x_p2_x == 0.0)) || ((_x_p2_l0 && _x_p2_l1) && (p2_x == _x_p2_x))))) || ( !((p2_l0 && ( !p2_l1)) && ((turn1 && ( !turn0)) && (delta == 0.0)))))) && (((max_prop == _x_p2_saved_max) && (((( !_x_p2_l0) && ( !_x_p2_l1)) && (p2_x == _x_p2_x)) && ((_x_id0 && _x_id1) && ( !(proposed2 <= _x_proposed2))))) || ( !((p2_l0 && p2_l1) && ((turn1 && ( !turn0)) && (delta == 0.0)))))) && (((((((((((( !_x_p1_l0) && ( !_x_p1_l1)) || (_x_p1_l0 && ( !_x_p1_l1))) || ((_x_p1_l1 && ( !_x_p1_l0)) || (_x_p1_l0 && _x_p1_l1))) && ( !(_x_proposed1 <= 0.0))) && ((_x_p1_x <= _x_proposed1) || ( !(_x_p1_l1 && ( !_x_p1_l0))))) && (((((p1_l0 == _x_p1_l0) && (p1_l1 == _x_p1_l1)) && ((delta + (p1_x + (-1.0 * _x_p1_x))) == 0.0)) && ((p1_saved_max == _x_p1_saved_max) && (proposed1 == _x_proposed1))) || ( !(( !(delta <= 0.0)) || ( !(turn0 && ( !turn1))))))) && (((((_x_p1_l1 && ( !_x_p1_l0)) && (_x_p1_x == 0.0)) && (((id0 == _x_id0) && (id1 == _x_id1)) && (proposed1 == _x_proposed1))) && (max_prop == _x_p1_saved_max)) || ( !((( !p1_l0) && ( !p1_l1)) && ((turn0 && ( !turn1)) && (delta == 0.0)))))) && (((max_prop == _x_p1_saved_max) && (((_x_p1_l0 && ( !_x_p1_l1)) && (_x_p1_x == 0.0)) && ((_x_id0 && ( !_x_id1)) && (proposed1 == _x_proposed1)))) || ( !((p1_l1 && ( !p1_l0)) && ((turn0 && ( !turn1)) && (delta == 0.0)))))) && (((((id0 == _x_id0) && (id1 == _x_id1)) && (proposed1 == _x_proposed1)) && ((max_prop == _x_p1_saved_max) && (((( !_x_p1_l0) && ( !_x_p1_l1)) && (_x_p1_x == 0.0)) || ((_x_p1_l0 && _x_p1_l1) && (p1_x == _x_p1_x))))) || ( !((p1_l0 && ( !p1_l1)) && ((turn0 && ( !turn1)) && (delta == 0.0)))))) && (((max_prop == _x_p1_saved_max) && (((( !_x_p1_l0) && ( !_x_p1_l1)) && (p1_x == _x_p1_x)) && ((_x_id0 && _x_id1) && ( !(proposed1 <= _x_proposed1))))) || ( !((p1_l0 && p1_l1) && ((turn0 && ( !turn1)) && (delta == 0.0)))))) && (((((((((((( !_x_p0_l0) && ( !_x_p0_l1)) || (_x_p0_l0 && ( !_x_p0_l1))) || ((_x_p0_l1 && ( !_x_p0_l0)) || (_x_p0_l0 && _x_p0_l1))) && ( !(_x_proposed0 <= 0.0))) && ((_x_p0_x <= _x_proposed0) || ( !(_x_p0_l1 && ( !_x_p0_l0))))) && (((((p0_l0 == _x_p0_l0) && (p0_l1 == _x_p0_l1)) && ((delta + (p0_x + (-1.0 * _x_p0_x))) == 0.0)) && ((p0_saved_max == _x_p0_saved_max) && (proposed0 == _x_proposed0))) || ( !(( !(delta <= 0.0)) || ( !(( !turn0) && ( !turn1))))))) && (((((_x_p0_l1 && ( !_x_p0_l0)) && (_x_p0_x == 0.0)) && (((id0 == _x_id0) && (id1 == _x_id1)) && (proposed0 == _x_proposed0))) && (max_prop == _x_p0_saved_max)) || ( !((( !p0_l0) && ( !p0_l1)) && ((( !turn0) && ( !turn1)) && (delta == 0.0)))))) && (((max_prop == _x_p0_saved_max) && (((_x_p0_l0 && ( !_x_p0_l1)) && (_x_p0_x == 0.0)) && ((( !_x_id0) && ( !_x_id1)) && (proposed0 == _x_proposed0)))) || ( !((p0_l1 && ( !p0_l0)) && ((( !turn0) && ( !turn1)) && (delta == 0.0)))))) && (((((id0 == _x_id0) && (id1 == _x_id1)) && (proposed0 == _x_proposed0)) && ((max_prop == _x_p0_saved_max) && (((( !_x_p0_l0) && ( !_x_p0_l1)) && (_x_p0_x == 0.0)) || ((_x_p0_l0 && _x_p0_l1) && (p0_x == _x_p0_x))))) || ( !((p0_l0 && ( !p0_l1)) && ((( !turn0) && ( !turn1)) && (delta == 0.0)))))) && (((max_prop == _x_p0_saved_max) && (((( !_x_p0_l0) && ( !_x_p0_l1)) && (p0_x == _x_p0_x)) && ((_x_id0 && _x_id1) && ( !(proposed0 <= _x_proposed0))))) || ( !((p0_l0 && p0_l1) && ((( !turn0) && ( !turn1)) && (delta == 0.0)))))) && ((((((((((_x_id0 && _x_id1) || ((_x_id1 && ( !_x_id0)) || ((( !_x_id0) && ( !_x_id1)) || (_x_id0 && ( !_x_id1))))) && ((_x_turn1 && ( !_x_turn0)) || ((( !_x_turn0) && ( !_x_turn1)) || (_x_turn0 && ( !_x_turn1))))) && ((delta <= 0.0) || (_x_inc_max_prop && (((id0 == _x_id0) && (id1 == _x_id1)) && ((turn0 == _x_turn0) && (turn1 == _x_turn1)))))) && (0.0 <= _x_delta)) && (_x_proposed0 <= _x_max_prop)) && (_x_proposed1 <= _x_max_prop)) && (_x_proposed2 <= _x_max_prop)) && (((_x_proposed0 == _x_max_prop) || (_x_proposed1 == _x_max_prop)) || (_x_proposed2 == _x_max_prop))) && (_x_inc_max_prop == (max_prop <= _x_max_prop)))))) && (((delta == _x__diverge_delta) || ( !(1.0 <= _diverge_delta))) && ((1.0 <= _diverge_delta) || ((delta + (_diverge_delta + (-1.0 * _x__diverge_delta))) == 0.0)))) && ((((((_EL_U_448 == (_x__EL_U_448 || ( !(_x__EL_U_446 || (1.0 <= _x__diverge_delta))))) && ((_EL_U_446 == (_x__EL_U_446 || (1.0 <= _x__diverge_delta))) && ((_EL_U_451 == (_x__EL_U_451 || ( !_x_inc_max_prop))) && (_EL_U_453 == (_x__EL_U_453 || ( !(_x__EL_U_451 || ( !_x_inc_max_prop)))))))) && (_x__J473 == (( !(((_J473 && _J479) && _J485) && _J491)) && ((((_J473 && _J479) && _J485) && _J491) || ((( !inc_max_prop) || ( !(( !inc_max_prop) || _EL_U_451))) || _J473))))) && (_x__J479 == (( !(((_J473 && _J479) && _J485) && _J491)) && ((((_J473 && _J479) && _J485) && _J491) || ((( !(( !inc_max_prop) || _EL_U_451)) || ( !(_EL_U_453 || ( !(( !inc_max_prop) || _EL_U_451))))) || _J479))))) && (_x__J485 == (( !(((_J473 && _J479) && _J485) && _J491)) && ((((_J473 && _J479) && _J485) && _J491) || (((1.0 <= _diverge_delta) || ( !((1.0 <= _diverge_delta) || _EL_U_446))) || _J485))))) && (_x__J491 == (( !(((_J473 && _J479) && _J485) && _J491)) && ((((_J473 && _J479) && _J485) && _J491) || ((( !((1.0 <= _diverge_delta) || _EL_U_446)) || ( !(_EL_U_448 || ( !((1.0 <= _diverge_delta) || _EL_U_446))))) || _J491))))));
    _J491 = _x__J491;
    _diverge_delta = _x__diverge_delta;
    delta = _x_delta;
    _J485 = _x__J485;
    max_prop = _x_max_prop;
    proposed2 = _x_proposed2;
    _J479 = _x__J479;
    proposed1 = _x_proposed1;
    _J473 = _x__J473;
    proposed0 = _x_proposed0;
    _EL_U_446 = _x__EL_U_446;
    _EL_U_448 = _x__EL_U_448;
    _EL_U_451 = _x__EL_U_451;
    inc_max_prop = _x_inc_max_prop;
    id1 = _x_id1;
    _EL_U_453 = _x__EL_U_453;
    id0 = _x_id0;
    turn1 = _x_turn1;
    turn0 = _x_turn0;
    p0_l0 = _x_p0_l0;
    p0_l1 = _x_p0_l1;
    p0_x = _x_p0_x;
    p0_saved_max = _x_p0_saved_max;
    p1_l0 = _x_p1_l0;
    p1_l1 = _x_p1_l1;
    p1_x = _x_p1_x;
    p1_saved_max = _x_p1_saved_max;
    p2_l0 = _x_p2_l0;
    p2_l1 = _x_p2_l1;
    p2_x = _x_p2_x;
    p2_saved_max = _x_p2_saved_max;

  }
}
