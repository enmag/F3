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
bool s1_evt1, _x_s1_evt1;
bool s1_evt0, _x_s1_evt0;
float r_x, _x_r_x;
bool r_l, _x_r_l;
int r_counter, _x_r_counter;
int r_evt_id, _x_r_evt_id;
bool r_event0, _x_r_event0;
bool r_event1, _x_r_event1;
bool _J657, _x__J657;
bool _J651, _x__J651;
bool _J645, _x__J645;
bool _J639, _x__J639;
bool _EL_U_613, _x__EL_U_613;
bool s0_l1, _x_s0_l1;
bool _EL_U_615, _x__EL_U_615;
bool s0_l0, _x_s0_l0;
bool _EL_U_617, _x__EL_U_617;
bool s0_l2, _x_s0_l2;
bool _EL_U_619, _x__EL_U_619;
float s0_x, _x_s0_x;
float s0_z, _x_s0_z;
float s0_y, _x_s0_y;
bool s0_evt1, _x_s0_evt1;
bool s0_evt0, _x_s0_evt0;
bool s1_l1, _x_s1_l1;
bool s1_l0, _x_s1_l0;
bool s1_l2, _x_s1_l2;
float s1_x, _x_s1_x;
float s1_z, _x_s1_z;
float s1_y, _x_s1_y;

  int __steps_to_fair = __VERIFIER_nondet_int();
  _diverge_delta = __VERIFIER_nondet_float();
  delta = __VERIFIER_nondet_float();
  s1_evt1 = __VERIFIER_nondet_bool();
  s1_evt0 = __VERIFIER_nondet_bool();
  r_x = __VERIFIER_nondet_float();
  r_l = __VERIFIER_nondet_bool();
  r_counter = __VERIFIER_nondet_int();
  r_evt_id = __VERIFIER_nondet_int();
  r_event0 = __VERIFIER_nondet_bool();
  r_event1 = __VERIFIER_nondet_bool();
  _J657 = __VERIFIER_nondet_bool();
  _J651 = __VERIFIER_nondet_bool();
  _J645 = __VERIFIER_nondet_bool();
  _J639 = __VERIFIER_nondet_bool();
  _EL_U_613 = __VERIFIER_nondet_bool();
  s0_l1 = __VERIFIER_nondet_bool();
  _EL_U_615 = __VERIFIER_nondet_bool();
  s0_l0 = __VERIFIER_nondet_bool();
  _EL_U_617 = __VERIFIER_nondet_bool();
  s0_l2 = __VERIFIER_nondet_bool();
  _EL_U_619 = __VERIFIER_nondet_bool();
  s0_x = __VERIFIER_nondet_float();
  s0_z = __VERIFIER_nondet_float();
  s0_y = __VERIFIER_nondet_float();
  s0_evt1 = __VERIFIER_nondet_bool();
  s0_evt0 = __VERIFIER_nondet_bool();
  s1_l1 = __VERIFIER_nondet_bool();
  s1_l0 = __VERIFIER_nondet_bool();
  s1_l2 = __VERIFIER_nondet_bool();
  s1_x = __VERIFIER_nondet_float();
  s1_z = __VERIFIER_nondet_float();
  s1_y = __VERIFIER_nondet_float();

  bool __ok = (((((((((((( !s1_evt0) && ( !s1_evt1)) || (s1_evt0 && ( !s1_evt1))) || ((s1_evt1 && ( !s1_evt0)) || (s1_evt0 && s1_evt1))) && ((((( !s1_l2) && (( !s1_l0) && ( !s1_l1))) || (( !s1_l2) && (s1_l0 && ( !s1_l1)))) || ((( !s1_l2) && (s1_l1 && ( !s1_l0))) || (( !s1_l2) && (s1_l0 && s1_l1)))) || ((s1_l2 && (( !s1_l0) && ( !s1_l1))) || (s1_l2 && (s1_l0 && ( !s1_l1)))))) && (((( !s1_l2) && (( !s1_l0) && ( !s1_l1))) && (s1_x == 0.0)) && ((s1_y == 0.0) && (s1_z == 0.0)))) && ((s1_x <= 20.0) || ( !(( !s1_l2) && (s1_l0 && ( !s1_l1)))))) && ((s1_x <= 120.0) || ( !(( !s1_l2) && (s1_l1 && ( !s1_l0)))))) && ((s1_x <= 120.0) || ( !(s1_l2 && (s1_l0 && ( !s1_l1)))))) && (((((((((( !s0_evt0) && ( !s0_evt1)) || (s0_evt0 && ( !s0_evt1))) || ((s0_evt1 && ( !s0_evt0)) || (s0_evt0 && s0_evt1))) && ((((( !s0_l2) && (( !s0_l0) && ( !s0_l1))) || (( !s0_l2) && (s0_l0 && ( !s0_l1)))) || ((( !s0_l2) && (s0_l1 && ( !s0_l0))) || (( !s0_l2) && (s0_l0 && s0_l1)))) || ((s0_l2 && (( !s0_l0) && ( !s0_l1))) || (s0_l2 && (s0_l0 && ( !s0_l1)))))) && (((( !s0_l2) && (( !s0_l0) && ( !s0_l1))) && (s0_x == 0.0)) && ((s0_y == 0.0) && (s0_z == 0.0)))) && ((s0_x <= 20.0) || ( !(( !s0_l2) && (s0_l0 && ( !s0_l1)))))) && ((s0_x <= 120.0) || ( !(( !s0_l2) && (s0_l1 && ( !s0_l0)))))) && ((s0_x <= 120.0) || ( !(s0_l2 && (s0_l0 && ( !s0_l1)))))) && ((((((r_l && ((r_counter == 0) && (r_x == 0.0))) && ((( !r_event0) && ( !r_event1)) || ((r_event0 && ( !r_event1)) || (r_event1 && ( !r_event0))))) && ((r_evt_id == 0) || (r_evt_id == 1))) && ((r_counter == 0) || (r_counter == 1))) && (( !r_l) || (r_x <= 0.0))) && (0.0 <= delta)))) && (delta == _diverge_delta)) && ((((( !(( !(_EL_U_619 || ( !((s0_l2 && (s0_l0 && ( !s0_l1))) || _EL_U_617)))) || (_EL_U_615 || ( !((1.0 <= _diverge_delta) || _EL_U_613))))) && ( !_J639)) && ( !_J645)) && ( !_J651)) && ( !_J657)));
  while (__steps_to_fair >= 0 && __ok) {
    if ((((_J639 && _J645) && _J651) && _J657)) {
      __steps_to_fair = __VERIFIER_nondet_int();
    } else {
      __steps_to_fair--;
    }
    _x__diverge_delta = __VERIFIER_nondet_float();
    _x_delta = __VERIFIER_nondet_float();
    _x_s1_evt1 = __VERIFIER_nondet_bool();
    _x_s1_evt0 = __VERIFIER_nondet_bool();
    _x_r_x = __VERIFIER_nondet_float();
    _x_r_l = __VERIFIER_nondet_bool();
    _x_r_counter = __VERIFIER_nondet_int();
    _x_r_evt_id = __VERIFIER_nondet_int();
    _x_r_event0 = __VERIFIER_nondet_bool();
    _x_r_event1 = __VERIFIER_nondet_bool();
    _x__J657 = __VERIFIER_nondet_bool();
    _x__J651 = __VERIFIER_nondet_bool();
    _x__J645 = __VERIFIER_nondet_bool();
    _x__J639 = __VERIFIER_nondet_bool();
    _x__EL_U_613 = __VERIFIER_nondet_bool();
    _x_s0_l1 = __VERIFIER_nondet_bool();
    _x__EL_U_615 = __VERIFIER_nondet_bool();
    _x_s0_l0 = __VERIFIER_nondet_bool();
    _x__EL_U_617 = __VERIFIER_nondet_bool();
    _x_s0_l2 = __VERIFIER_nondet_bool();
    _x__EL_U_619 = __VERIFIER_nondet_bool();
    _x_s0_x = __VERIFIER_nondet_float();
    _x_s0_z = __VERIFIER_nondet_float();
    _x_s0_y = __VERIFIER_nondet_float();
    _x_s0_evt1 = __VERIFIER_nondet_bool();
    _x_s0_evt0 = __VERIFIER_nondet_bool();
    _x_s1_l1 = __VERIFIER_nondet_bool();
    _x_s1_l0 = __VERIFIER_nondet_bool();
    _x_s1_l2 = __VERIFIER_nondet_bool();
    _x_s1_x = __VERIFIER_nondet_float();
    _x_s1_z = __VERIFIER_nondet_float();
    _x_s1_y = __VERIFIER_nondet_float();

    __ok = (((((((((((((((((((((((((((( !_x_s1_evt0) && ( !_x_s1_evt1)) || (_x_s1_evt0 && ( !_x_s1_evt1))) || ((_x_s1_evt1 && ( !_x_s1_evt0)) || (_x_s1_evt0 && _x_s1_evt1))) && ((((( !_x_s1_l2) && (( !_x_s1_l0) && ( !_x_s1_l1))) || (( !_x_s1_l2) && (_x_s1_l0 && ( !_x_s1_l1)))) || ((( !_x_s1_l2) && (_x_s1_l1 && ( !_x_s1_l0))) || (( !_x_s1_l2) && (_x_s1_l0 && _x_s1_l1)))) || ((_x_s1_l2 && (( !_x_s1_l0) && ( !_x_s1_l1))) || (_x_s1_l2 && (_x_s1_l0 && ( !_x_s1_l1)))))) && ((_x_s1_x <= 20.0) || ( !(( !_x_s1_l2) && (_x_s1_l0 && ( !_x_s1_l1)))))) && ((_x_s1_x <= 120.0) || ( !(( !_x_s1_l2) && (_x_s1_l1 && ( !_x_s1_l0)))))) && ((_x_s1_x <= 120.0) || ( !(_x_s1_l2 && (_x_s1_l0 && ( !_x_s1_l1)))))) && ((delta <= 0.0) || ((((delta + (s1_x + (-1.0 * _x_s1_x))) == 0.0) && ((delta + (s1_y + (-1.0 * _x_s1_y))) == 0.0)) && ((((s1_l0 == _x_s1_l0) && (s1_l1 == _x_s1_l1)) && (s1_l2 == _x_s1_l2)) && ((delta + (s1_z + (-1.0 * _x_s1_z))) == 0.0))))) && ((((((s1_l0 == _x_s1_l0) && (s1_l1 == _x_s1_l1)) && (s1_l2 == _x_s1_l2)) && ((delta + (s1_x + (-1.0 * _x_s1_x))) == 0.0)) && (((delta + (s1_y + (-1.0 * _x_s1_y))) == 0.0) && ((delta + (s1_z + (-1.0 * _x_s1_z))) == 0.0))) || ( !(( !s1_evt0) && ( !s1_evt1))))) && (((((s1_evt0 && s1_evt1) && (( !_x_s1_l2) && (_x_s1_l0 && ( !_x_s1_l1)))) && ((_x_s1_x == 0.0) && (_x_s1_y == 0.0))) && (s1_z == _x_s1_z)) || ( !((( !s1_l2) && (( !s1_l0) && ( !s1_l1))) && ((delta == 0.0) && ( !(( !s1_evt0) && ( !s1_evt1)))))))) && (((((( !_x_s1_l2) && (_x_s1_l1 && ( !_x_s1_l0))) || (( !_x_s1_l2) && (_x_s1_l0 && _x_s1_l1))) && (s1_x == _x_s1_x)) && ((s1_z == _x_s1_z) && (s1_y == _x_s1_y))) || ( !((( !s1_l2) && (s1_l0 && ( !s1_l1))) && ((delta == 0.0) && ( !(( !s1_evt0) && ( !s1_evt1)))))))) && (((s1_evt0 && ( !s1_evt1)) && ((20.0 <= s1_x) && ( !(120.0 <= s1_z)))) || ( !(((delta == 0.0) && ( !(( !s1_evt0) && ( !s1_evt1)))) && ((( !s1_l2) && (s1_l0 && ( !s1_l1))) && (( !_x_s1_l2) && (_x_s1_l1 && ( !_x_s1_l0)))))))) && (((s1_evt1 && ( !s1_evt0)) && ((20.0 <= s1_x) && (120.0 <= s1_z))) || ( !(((delta == 0.0) && ( !(( !s1_evt0) && ( !s1_evt1)))) && ((( !s1_l2) && (s1_l0 && ( !s1_l1))) && (( !_x_s1_l2) && (_x_s1_l0 && _x_s1_l1))))))) && (((s1_z == _x_s1_z) && (((s1_evt1 && ( !s1_evt0)) && (( !_x_s1_l2) && (_x_s1_l0 && _x_s1_l1))) && ((s1_x == _x_s1_x) && (s1_y == _x_s1_y)))) || ( !((( !s1_l2) && (s1_l1 && ( !s1_l0))) && ((delta == 0.0) && ( !(( !s1_evt0) && ( !s1_evt1)))))))) && (((((s1_evt0 && s1_evt1) && (_x_s1_l2 && (( !_x_s1_l0) && ( !_x_s1_l1)))) && ((_x_s1_x == 0.0) && (s1_y == _x_s1_y))) && (_x_s1_z == 0.0)) || ( !((( !s1_l2) && (s1_l0 && s1_l1)) && ((delta == 0.0) && ( !(( !s1_evt0) && ( !s1_evt1)))))))) && ((((s1_x == _x_s1_x) && (s1_y == _x_s1_y)) && ((s1_z == _x_s1_z) && ((( !_x_s1_l2) && (( !_x_s1_l0) && ( !_x_s1_l1))) || (_x_s1_l2 && (_x_s1_l0 && ( !_x_s1_l1)))))) || ( !((s1_l2 && (( !s1_l0) && ( !s1_l1))) && ((delta == 0.0) && ( !(( !s1_evt0) && ( !s1_evt1)))))))) && (((s1_evt0 && ( !s1_evt1)) && ((20.0 <= s1_x) && ( !(120.0 <= s1_y)))) || ( !(((delta == 0.0) && ( !(( !s1_evt0) && ( !s1_evt1)))) && ((s1_l2 && (( !s1_l0) && ( !s1_l1))) && (_x_s1_l2 && (_x_s1_l0 && ( !_x_s1_l1)))))))) && (((s1_evt1 && ( !s1_evt0)) && ((20.0 <= s1_x) && (120.0 <= s1_y))) || ( !(((delta == 0.0) && ( !(( !s1_evt0) && ( !s1_evt1)))) && ((( !_x_s1_l2) && (( !_x_s1_l0) && ( !_x_s1_l1))) && (s1_l2 && (( !s1_l0) && ( !s1_l1)))))))) && (((s1_z == _x_s1_z) && (((s1_x == _x_s1_x) && (s1_y == _x_s1_y)) && ((s1_evt1 && ( !s1_evt0)) && (( !_x_s1_l2) && (( !_x_s1_l0) && ( !_x_s1_l1)))))) || ( !((s1_l2 && (s1_l0 && ( !s1_l1))) && ((delta == 0.0) && ( !(( !s1_evt0) && ( !s1_evt1)))))))) && ((((((((((((((((((((( !_x_s0_evt0) && ( !_x_s0_evt1)) || (_x_s0_evt0 && ( !_x_s0_evt1))) || ((_x_s0_evt1 && ( !_x_s0_evt0)) || (_x_s0_evt0 && _x_s0_evt1))) && ((((( !_x_s0_l2) && (( !_x_s0_l0) && ( !_x_s0_l1))) || (( !_x_s0_l2) && (_x_s0_l0 && ( !_x_s0_l1)))) || ((( !_x_s0_l2) && (_x_s0_l1 && ( !_x_s0_l0))) || (( !_x_s0_l2) && (_x_s0_l0 && _x_s0_l1)))) || ((_x_s0_l2 && (( !_x_s0_l0) && ( !_x_s0_l1))) || (_x_s0_l2 && (_x_s0_l0 && ( !_x_s0_l1)))))) && ((_x_s0_x <= 20.0) || ( !(( !_x_s0_l2) && (_x_s0_l0 && ( !_x_s0_l1)))))) && ((_x_s0_x <= 120.0) || ( !(( !_x_s0_l2) && (_x_s0_l1 && ( !_x_s0_l0)))))) && ((_x_s0_x <= 120.0) || ( !(_x_s0_l2 && (_x_s0_l0 && ( !_x_s0_l1)))))) && ((delta <= 0.0) || ((((delta + (s0_x + (-1.0 * _x_s0_x))) == 0.0) && ((delta + (s0_y + (-1.0 * _x_s0_y))) == 0.0)) && ((((s0_l0 == _x_s0_l0) && (s0_l1 == _x_s0_l1)) && (s0_l2 == _x_s0_l2)) && ((delta + (s0_z + (-1.0 * _x_s0_z))) == 0.0))))) && ((((((s0_l0 == _x_s0_l0) && (s0_l1 == _x_s0_l1)) && (s0_l2 == _x_s0_l2)) && ((delta + (s0_x + (-1.0 * _x_s0_x))) == 0.0)) && (((delta + (s0_y + (-1.0 * _x_s0_y))) == 0.0) && ((delta + (s0_z + (-1.0 * _x_s0_z))) == 0.0))) || ( !(( !s0_evt0) && ( !s0_evt1))))) && (((((s0_evt0 && s0_evt1) && (( !_x_s0_l2) && (_x_s0_l0 && ( !_x_s0_l1)))) && ((_x_s0_x == 0.0) && (_x_s0_y == 0.0))) && (s0_z == _x_s0_z)) || ( !((( !s0_l2) && (( !s0_l0) && ( !s0_l1))) && ((delta == 0.0) && ( !(( !s0_evt0) && ( !s0_evt1)))))))) && (((((( !_x_s0_l2) && (_x_s0_l1 && ( !_x_s0_l0))) || (( !_x_s0_l2) && (_x_s0_l0 && _x_s0_l1))) && (s0_x == _x_s0_x)) && ((s0_z == _x_s0_z) && (s0_y == _x_s0_y))) || ( !((( !s0_l2) && (s0_l0 && ( !s0_l1))) && ((delta == 0.0) && ( !(( !s0_evt0) && ( !s0_evt1)))))))) && (((s0_evt0 && ( !s0_evt1)) && ((20.0 <= s0_x) && ( !(120.0 <= s0_z)))) || ( !(((delta == 0.0) && ( !(( !s0_evt0) && ( !s0_evt1)))) && ((( !s0_l2) && (s0_l0 && ( !s0_l1))) && (( !_x_s0_l2) && (_x_s0_l1 && ( !_x_s0_l0)))))))) && (((s0_evt1 && ( !s0_evt0)) && ((20.0 <= s0_x) && (120.0 <= s0_z))) || ( !(((delta == 0.0) && ( !(( !s0_evt0) && ( !s0_evt1)))) && ((( !s0_l2) && (s0_l0 && ( !s0_l1))) && (( !_x_s0_l2) && (_x_s0_l0 && _x_s0_l1))))))) && (((s0_z == _x_s0_z) && (((s0_evt1 && ( !s0_evt0)) && (( !_x_s0_l2) && (_x_s0_l0 && _x_s0_l1))) && ((s0_x == _x_s0_x) && (s0_y == _x_s0_y)))) || ( !((( !s0_l2) && (s0_l1 && ( !s0_l0))) && ((delta == 0.0) && ( !(( !s0_evt0) && ( !s0_evt1)))))))) && (((((s0_evt0 && s0_evt1) && (_x_s0_l2 && (( !_x_s0_l0) && ( !_x_s0_l1)))) && ((_x_s0_x == 0.0) && (s0_y == _x_s0_y))) && (_x_s0_z == 0.0)) || ( !((( !s0_l2) && (s0_l0 && s0_l1)) && ((delta == 0.0) && ( !(( !s0_evt0) && ( !s0_evt1)))))))) && ((((s0_x == _x_s0_x) && (s0_y == _x_s0_y)) && ((s0_z == _x_s0_z) && ((( !_x_s0_l2) && (( !_x_s0_l0) && ( !_x_s0_l1))) || (_x_s0_l2 && (_x_s0_l0 && ( !_x_s0_l1)))))) || ( !((s0_l2 && (( !s0_l0) && ( !s0_l1))) && ((delta == 0.0) && ( !(( !s0_evt0) && ( !s0_evt1)))))))) && (((s0_evt0 && ( !s0_evt1)) && ((20.0 <= s0_x) && ( !(120.0 <= s0_y)))) || ( !(((delta == 0.0) && ( !(( !s0_evt0) && ( !s0_evt1)))) && ((s0_l2 && (( !s0_l0) && ( !s0_l1))) && (_x_s0_l2 && (_x_s0_l0 && ( !_x_s0_l1)))))))) && (((s0_evt1 && ( !s0_evt0)) && ((20.0 <= s0_x) && (120.0 <= s0_y))) || ( !(((delta == 0.0) && ( !(( !s0_evt0) && ( !s0_evt1)))) && ((( !_x_s0_l2) && (( !_x_s0_l0) && ( !_x_s0_l1))) && (s0_l2 && (( !s0_l0) && ( !s0_l1)))))))) && (((s0_z == _x_s0_z) && (((s0_x == _x_s0_x) && (s0_y == _x_s0_y)) && ((s0_evt1 && ( !s0_evt0)) && (( !_x_s0_l2) && (( !_x_s0_l0) && ( !_x_s0_l1)))))) || ( !((s0_l2 && (s0_l0 && ( !s0_l1))) && ((delta == 0.0) && ( !(( !s0_evt0) && ( !s0_evt1)))))))) && ((((((((((_x_r_evt_id == 0) || (_x_r_evt_id == 1)) && ((_x_r_counter == 0) || (_x_r_counter == 1))) && (( !_x_r_l) || (_x_r_x <= 0.0))) && ((delta <= 0.0) || (((delta + (r_x + (-1.0 * _x_r_x))) == 0.0) && ((r_l == _x_r_l) && (r_counter == _x_r_counter))))) && (((r_l == _x_r_l) && (((delta + (r_x + (-1.0 * _x_r_x))) == 0.0) && (r_counter == _x_r_counter))) || ( !(( !r_event0) && ( !r_event1))))) && (((((r_event1 && ( !r_event0)) && (r_x <= 0.0)) && (( !_x_r_l) && (r_evt_id == r_counter))) && ((r_counter == _x_r_counter) && (r_x == _x_r_x))) || ( !(r_l && (( !(( !r_event0) && ( !r_event1))) && (delta == 0.0)))))) && ((_x_r_l && (((r_event0 && ( !r_event1)) && (r_evt_id == r_counter)) && ((_x_r_x == 0.0) && ((r_counter + (-1 * _x_r_counter)) == -1)))) || ( !((( !(( !r_event0) && ( !r_event1))) && (delta == 0.0)) && (( !r_l) && ( !(1 <= r_counter))))))) && ((_x_r_l && (((r_event0 && ( !r_event1)) && (r_evt_id == r_counter)) && ((_x_r_counter == 0) && (_x_r_x == 0.0)))) || ( !((( !(( !r_event0) && ( !r_event1))) && (delta == 0.0)) && (( !r_l) && (r_counter == 1)))))) && (0.0 <= _x_delta)))) && ((( !(( !s1_evt0) && ( !s1_evt1))) || (( !(( !r_event0) && ( !r_event1))) || ( !(( !s0_evt0) && ( !s0_evt1))))) || ( !(delta == 0.0)))) && (( !(delta == 0.0)) || ((s0_evt1 && ( !s0_evt0)) == ((r_event0 && ( !r_event1)) && (r_evt_id == 0))))) && (( !(delta == 0.0)) || ((s0_evt0 && s0_evt1) == ((r_event1 && ( !r_event0)) && (r_evt_id == 0))))) && (( !(delta == 0.0)) || ((s1_evt1 && ( !s1_evt0)) == ((r_event0 && ( !r_event1)) && (r_evt_id == 1))))) && (( !(delta == 0.0)) || ((s1_evt0 && s1_evt1) == ((r_event1 && ( !r_event0)) && (r_evt_id == 1))))) && (((delta == _x__diverge_delta) || ( !(1.0 <= _diverge_delta))) && ((1.0 <= _diverge_delta) || ((delta + (_diverge_delta + (-1.0 * _x__diverge_delta))) == 0.0)))) && ((((((_EL_U_615 == (_x__EL_U_615 || ( !(_x__EL_U_613 || (1.0 <= _x__diverge_delta))))) && ((_EL_U_613 == (_x__EL_U_613 || (1.0 <= _x__diverge_delta))) && ((_EL_U_617 == ((_x_s0_l2 && (_x_s0_l0 && ( !_x_s0_l1))) || _x__EL_U_617)) && (_EL_U_619 == (_x__EL_U_619 || ( !((_x_s0_l2 && (_x_s0_l0 && ( !_x_s0_l1))) || _x__EL_U_617))))))) && (_x__J639 == (( !(((_J639 && _J645) && _J651) && _J657)) && ((((_J639 && _J645) && _J651) && _J657) || (((s0_l2 && (s0_l0 && ( !s0_l1))) || ( !((s0_l2 && (s0_l0 && ( !s0_l1))) || _EL_U_617))) || _J639))))) && (_x__J645 == (( !(((_J639 && _J645) && _J651) && _J657)) && ((((_J639 && _J645) && _J651) && _J657) || ((( !((s0_l2 && (s0_l0 && ( !s0_l1))) || _EL_U_617)) || ( !(_EL_U_619 || ( !((s0_l2 && (s0_l0 && ( !s0_l1))) || _EL_U_617))))) || _J645))))) && (_x__J651 == (( !(((_J639 && _J645) && _J651) && _J657)) && ((((_J639 && _J645) && _J651) && _J657) || (((1.0 <= _diverge_delta) || ( !((1.0 <= _diverge_delta) || _EL_U_613))) || _J651))))) && (_x__J657 == (( !(((_J639 && _J645) && _J651) && _J657)) && ((((_J639 && _J645) && _J651) && _J657) || ((( !((1.0 <= _diverge_delta) || _EL_U_613)) || ( !(_EL_U_615 || ( !((1.0 <= _diverge_delta) || _EL_U_613))))) || _J657))))));
    _diverge_delta = _x__diverge_delta;
    delta = _x_delta;
    s1_evt1 = _x_s1_evt1;
    s1_evt0 = _x_s1_evt0;
    r_x = _x_r_x;
    r_l = _x_r_l;
    r_counter = _x_r_counter;
    r_evt_id = _x_r_evt_id;
    r_event0 = _x_r_event0;
    r_event1 = _x_r_event1;
    _J657 = _x__J657;
    _J651 = _x__J651;
    _J645 = _x__J645;
    _J639 = _x__J639;
    _EL_U_613 = _x__EL_U_613;
    s0_l1 = _x_s0_l1;
    _EL_U_615 = _x__EL_U_615;
    s0_l0 = _x_s0_l0;
    _EL_U_617 = _x__EL_U_617;
    s0_l2 = _x_s0_l2;
    _EL_U_619 = _x__EL_U_619;
    s0_x = _x_s0_x;
    s0_z = _x_s0_z;
    s0_y = _x_s0_y;
    s0_evt1 = _x_s0_evt1;
    s0_evt0 = _x_s0_evt0;
    s1_l1 = _x_s1_l1;
    s1_l0 = _x_s1_l0;
    s1_l2 = _x_s1_l2;
    s1_x = _x_s1_x;
    s1_z = _x_s1_z;
    s1_y = _x_s1_y;

  }
}
