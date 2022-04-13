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
int turn, _x_turn;
int id, _x_id;
bool p0_l0, _x_p0_l0;
bool p0_l1, _x_p0_l1;
float p0_x, _x_p0_x;
bool p1_l0, _x_p1_l0;
bool p1_l1, _x_p1_l1;
float p1_x, _x_p1_x;
bool _J336, _x__J336;
bool _J330, _x__J330;
bool _J323, _x__J323;
bool _J317, _x__J317;
bool _J312, _x__J312;
bool _J306, _x__J306;
bool _EL_U_269, _x__EL_U_269;
bool _EL_U_271, _x__EL_U_271;
bool _EL_U_273, _x__EL_U_273;
bool _EL_U_275, _x__EL_U_275;
bool _EL_U_277, _x__EL_U_277;
bool _EL_U_279, _x__EL_U_279;

  int __steps_to_fair = __VERIFIER_nondet_int();
  _diverge_delta = __VERIFIER_nondet_float();
  delta = __VERIFIER_nondet_float();
  turn = __VERIFIER_nondet_int();
  id = __VERIFIER_nondet_int();
  p0_l0 = __VERIFIER_nondet_bool();
  p0_l1 = __VERIFIER_nondet_bool();
  p0_x = __VERIFIER_nondet_float();
  p1_l0 = __VERIFIER_nondet_bool();
  p1_l1 = __VERIFIER_nondet_bool();
  p1_x = __VERIFIER_nondet_float();
  _J336 = __VERIFIER_nondet_bool();
  _J330 = __VERIFIER_nondet_bool();
  _J323 = __VERIFIER_nondet_bool();
  _J317 = __VERIFIER_nondet_bool();
  _J312 = __VERIFIER_nondet_bool();
  _J306 = __VERIFIER_nondet_bool();
  _EL_U_269 = __VERIFIER_nondet_bool();
  _EL_U_271 = __VERIFIER_nondet_bool();
  _EL_U_273 = __VERIFIER_nondet_bool();
  _EL_U_275 = __VERIFIER_nondet_bool();
  _EL_U_277 = __VERIFIER_nondet_bool();
  _EL_U_279 = __VERIFIER_nondet_bool();

  bool __ok = ((((id == 0) && (((((( !p1_l0) && ( !p1_l1)) && (p1_x == 0.0)) && (((( !p1_l0) && ( !p1_l1)) || (p1_l0 && ( !p1_l1))) || ((p1_l1 && ( !p1_l0)) || (p1_l0 && p1_l1)))) && ((p1_x <= 2.0) || ( !(p1_l1 && ( !p1_l0))))) && (((((( !p0_l0) && ( !p0_l1)) && (p0_x == 0.0)) && (((( !p0_l0) && ( !p0_l1)) || (p0_l0 && ( !p0_l1))) || ((p0_l1 && ( !p0_l0)) || (p0_l0 && p0_l1)))) && ((p0_x <= 2.0) || ( !(p0_l1 && ( !p0_l0))))) && (((0.0 <= delta) && ((id == 2) || ((id == 0) || (id == 1)))) && ((turn == 1) || (turn == 2)))))) && (delta == _diverge_delta)) && ((((((( !((( !(_EL_U_279 || ( !((p0_l0 && p0_l1) || _EL_U_277)))) || (_EL_U_275 || ( !((p0_l0 && ( !p0_l1)) || _EL_U_273)))) || (_EL_U_271 || ( !((1.0 <= _diverge_delta) || _EL_U_269))))) && ( !_J306)) && ( !_J312)) && ( !_J317)) && ( !_J323)) && ( !_J330)) && ( !_J336)));
  while (__steps_to_fair >= 0 && __ok) {
    if ((((((_J306 && _J312) && _J317) && _J323) && _J330) && _J336)) {
      __steps_to_fair = __VERIFIER_nondet_int();
    } else {
      __steps_to_fair--;
    }
    _x__diverge_delta = __VERIFIER_nondet_float();
    _x_delta = __VERIFIER_nondet_float();
    _x_turn = __VERIFIER_nondet_int();
    _x_id = __VERIFIER_nondet_int();
    _x_p0_l0 = __VERIFIER_nondet_bool();
    _x_p0_l1 = __VERIFIER_nondet_bool();
    _x_p0_x = __VERIFIER_nondet_float();
    _x_p1_l0 = __VERIFIER_nondet_bool();
    _x_p1_l1 = __VERIFIER_nondet_bool();
    _x_p1_x = __VERIFIER_nondet_float();
    _x__J336 = __VERIFIER_nondet_bool();
    _x__J330 = __VERIFIER_nondet_bool();
    _x__J323 = __VERIFIER_nondet_bool();
    _x__J317 = __VERIFIER_nondet_bool();
    _x__J312 = __VERIFIER_nondet_bool();
    _x__J306 = __VERIFIER_nondet_bool();
    _x__EL_U_269 = __VERIFIER_nondet_bool();
    _x__EL_U_271 = __VERIFIER_nondet_bool();
    _x__EL_U_273 = __VERIFIER_nondet_bool();
    _x__EL_U_275 = __VERIFIER_nondet_bool();
    _x__EL_U_277 = __VERIFIER_nondet_bool();
    _x__EL_U_279 = __VERIFIER_nondet_bool();

    __ok = ((((((((((((((( !_x_p1_l0) && ( !_x_p1_l1)) || (_x_p1_l0 && ( !_x_p1_l1))) || ((_x_p1_l1 && ( !_x_p1_l0)) || (_x_p1_l0 && _x_p1_l1))) && ((_x_p1_x <= 2.0) || ( !(_x_p1_l1 && ( !_x_p1_l0))))) && ((((p1_l0 == _x_p1_l0) && (p1_l1 == _x_p1_l1)) && ((delta + (p1_x + (-1.0 * _x_p1_x))) == 0.0)) || ( !(( !(delta <= 0.0)) || ( !(turn == 2)))))) && ((((id == 0) && (_x_p1_l1 && ( !_x_p1_l0))) && ((id == _x_id) && (_x_p1_x == 0.0))) || ( !((( !p1_l0) && ( !p1_l1)) && ((delta == 0.0) && (turn == 2)))))) && ((((_x_p1_l0 && ( !_x_p1_l1)) && (p1_x <= 2.0)) && ((_x_p1_x == 0.0) && (_x_id == 2))) || ( !((p1_l1 && ( !p1_l0)) && ((delta == 0.0) && (turn == 2)))))) && (((( !_x_p1_l0) && ( !_x_p1_l1)) || (_x_p1_l0 && _x_p1_l1)) || ( !((p1_l0 && ( !p1_l1)) && ((delta == 0.0) && (turn == 2)))))) && ((((id == _x_id) && (_x_p1_x == 0.0)) && (( !(p1_x <= 2.0)) && ( !(id == 2)))) || ( !(((delta == 0.0) && (turn == 2)) && ((( !_x_p1_l0) && ( !_x_p1_l1)) && (p1_l0 && ( !p1_l1))))))) && ((((id == _x_id) && (p1_x == _x_p1_x)) && (( !(p1_x <= 2.0)) && (id == 2))) || ( !(((delta == 0.0) && (turn == 2)) && ((p1_l0 && ( !p1_l1)) && (_x_p1_l0 && _x_p1_l1)))))) && (((( !_x_p1_l0) && ( !_x_p1_l1)) && ((_x_id == 0) && (p1_x == _x_p1_x))) || ( !((p1_l0 && p1_l1) && ((delta == 0.0) && (turn == 2)))))) && ((((((((((((( !_x_p0_l0) && ( !_x_p0_l1)) || (_x_p0_l0 && ( !_x_p0_l1))) || ((_x_p0_l1 && ( !_x_p0_l0)) || (_x_p0_l0 && _x_p0_l1))) && ((_x_p0_x <= 2.0) || ( !(_x_p0_l1 && ( !_x_p0_l0))))) && ((((p0_l0 == _x_p0_l0) && (p0_l1 == _x_p0_l1)) && ((delta + (p0_x + (-1.0 * _x_p0_x))) == 0.0)) || ( !(( !(delta <= 0.0)) || ( !(turn == 1)))))) && ((((_x_p0_l1 && ( !_x_p0_l0)) && (id == 0)) && ((_x_p0_x == 0.0) && (id == _x_id))) || ( !((( !p0_l0) && ( !p0_l1)) && ((turn == 1) && (delta == 0.0)))))) && ((((_x_p0_l0 && ( !_x_p0_l1)) && (p0_x <= 2.0)) && ((_x_p0_x == 0.0) && (_x_id == 1))) || ( !((p0_l1 && ( !p0_l0)) && ((turn == 1) && (delta == 0.0)))))) && (((( !_x_p0_l0) && ( !_x_p0_l1)) || (_x_p0_l0 && _x_p0_l1)) || ( !((p0_l0 && ( !p0_l1)) && ((turn == 1) && (delta == 0.0)))))) && ((((_x_p0_x == 0.0) && (id == _x_id)) && (( !(p0_x <= 2.0)) && ( !(id == 1)))) || ( !(((turn == 1) && (delta == 0.0)) && ((( !_x_p0_l0) && ( !_x_p0_l1)) && (p0_l0 && ( !p0_l1))))))) && ((((id == _x_id) && (p0_x == _x_p0_x)) && (( !(p0_x <= 2.0)) && (id == 1))) || ( !(((turn == 1) && (delta == 0.0)) && ((p0_l0 && ( !p0_l1)) && (_x_p0_l0 && _x_p0_l1)))))) && (((( !_x_p0_l0) && ( !_x_p0_l1)) && ((p0_x == _x_p0_x) && (_x_id == 0))) || ( !((p0_l0 && p0_l1) && ((turn == 1) && (delta == 0.0)))))) && (((((id == 2) || ((id == 0) || (id == 1))) && ((_x_turn == 1) || (_x_turn == 2))) && (0.0 <= _x_delta)) && ((delta <= 0.0) || ((id == _x_id) && (turn == _x_turn)))))) && (((delta == _x__diverge_delta) || ( !(1.0 <= _diverge_delta))) && ((1.0 <= _diverge_delta) || ((delta + (_diverge_delta + (-1.0 * _x__diverge_delta))) == 0.0)))) && ((((((((_EL_U_271 == (_x__EL_U_271 || ( !(_x__EL_U_269 || (1.0 <= _x__diverge_delta))))) && ((_EL_U_269 == (_x__EL_U_269 || (1.0 <= _x__diverge_delta))) && ((_EL_U_275 == (_x__EL_U_275 || ( !((_x_p0_l0 && ( !_x_p0_l1)) || _x__EL_U_273)))) && ((_EL_U_273 == ((_x_p0_l0 && ( !_x_p0_l1)) || _x__EL_U_273)) && ((_EL_U_277 == ((_x_p0_l0 && _x_p0_l1) || _x__EL_U_277)) && (_EL_U_279 == (_x__EL_U_279 || ( !((_x_p0_l0 && _x_p0_l1) || _x__EL_U_277))))))))) && (_x__J306 == (( !(((((_J306 && _J312) && _J317) && _J323) && _J330) && _J336)) && ((((((_J306 && _J312) && _J317) && _J323) && _J330) && _J336) || (((p0_l0 && p0_l1) || ( !((p0_l0 && p0_l1) || _EL_U_277))) || _J306))))) && (_x__J312 == (( !(((((_J306 && _J312) && _J317) && _J323) && _J330) && _J336)) && ((((((_J306 && _J312) && _J317) && _J323) && _J330) && _J336) || ((( !((p0_l0 && p0_l1) || _EL_U_277)) || ( !(_EL_U_279 || ( !((p0_l0 && p0_l1) || _EL_U_277))))) || _J312))))) && (_x__J317 == (( !(((((_J306 && _J312) && _J317) && _J323) && _J330) && _J336)) && ((((((_J306 && _J312) && _J317) && _J323) && _J330) && _J336) || (((p0_l0 && ( !p0_l1)) || ( !((p0_l0 && ( !p0_l1)) || _EL_U_273))) || _J317))))) && (_x__J323 == (( !(((((_J306 && _J312) && _J317) && _J323) && _J330) && _J336)) && ((((((_J306 && _J312) && _J317) && _J323) && _J330) && _J336) || ((( !((p0_l0 && ( !p0_l1)) || _EL_U_273)) || ( !(_EL_U_275 || ( !((p0_l0 && ( !p0_l1)) || _EL_U_273))))) || _J323))))) && (_x__J330 == (( !(((((_J306 && _J312) && _J317) && _J323) && _J330) && _J336)) && ((((((_J306 && _J312) && _J317) && _J323) && _J330) && _J336) || (((1.0 <= _diverge_delta) || ( !((1.0 <= _diverge_delta) || _EL_U_269))) || _J330))))) && (_x__J336 == (( !(((((_J306 && _J312) && _J317) && _J323) && _J330) && _J336)) && ((((((_J306 && _J312) && _J317) && _J323) && _J330) && _J336) || ((( !((1.0 <= _diverge_delta) || _EL_U_269)) || ( !(_EL_U_271 || ( !((1.0 <= _diverge_delta) || _EL_U_269))))) || _J336))))));
    _diverge_delta = _x__diverge_delta;
    delta = _x_delta;
    turn = _x_turn;
    id = _x_id;
    p0_l0 = _x_p0_l0;
    p0_l1 = _x_p0_l1;
    p0_x = _x_p0_x;
    p1_l0 = _x_p1_l0;
    p1_l1 = _x_p1_l1;
    p1_x = _x_p1_x;
    _J336 = _x__J336;
    _J330 = _x__J330;
    _J323 = _x__J323;
    _J317 = _x__J317;
    _J312 = _x__J312;
    _J306 = _x__J306;
    _EL_U_269 = _x__EL_U_269;
    _EL_U_271 = _x__EL_U_271;
    _EL_U_273 = _x__EL_U_273;
    _EL_U_275 = _x__EL_U_275;
    _EL_U_277 = _x__EL_U_277;
    _EL_U_279 = _x__EL_U_279;

  }
}
