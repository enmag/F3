extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);
typedef enum {false, true} bool;
bool __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}

int main()
{
int min_num, _x_min_num;
int num1, _x_num1;
int num0, _x_num0;
int max_num, _x_max_num;
bool p0_l1, _x_p0_l1;
bool p0_l0, _x_p0_l0;
bool p1_l1, _x_p1_l1;
bool p1_l0, _x_p1_l0;
bool _J267, _x__J267;
bool _J258, _x__J258;
bool _J252, _x__J252;
bool _J247, _x__J247;
bool _J241, _x__J241;
bool _EL_U_210, _x__EL_U_210;
bool _EL_U_211, _x__EL_U_211;
bool _EL_U_214, _x__EL_U_214;
bool _EL_U_216, _x__EL_U_216;
bool _EL_U_218, _x__EL_U_218;
bool run0, _x_run0;

  int __steps_to_fair = __VERIFIER_nondet_int();
  min_num = __VERIFIER_nondet_int();
  num1 = __VERIFIER_nondet_int();
  num0 = __VERIFIER_nondet_int();
  max_num = __VERIFIER_nondet_int();
  p0_l1 = __VERIFIER_nondet_bool();
  p0_l0 = __VERIFIER_nondet_bool();
  p1_l1 = __VERIFIER_nondet_bool();
  p1_l0 = __VERIFIER_nondet_bool();
  _J267 = __VERIFIER_nondet_bool();
  _J258 = __VERIFIER_nondet_bool();
  _J252 = __VERIFIER_nondet_bool();
  _J247 = __VERIFIER_nondet_bool();
  _J241 = __VERIFIER_nondet_bool();
  _EL_U_210 = __VERIFIER_nondet_bool();
  _EL_U_211 = __VERIFIER_nondet_bool();
  _EL_U_214 = __VERIFIER_nondet_bool();
  _EL_U_216 = __VERIFIER_nondet_bool();
  _EL_U_218 = __VERIFIER_nondet_bool();
  run0 = __VERIFIER_nondet_bool();

  bool __ok = ((((( !p1_l0) && ( !p1_l1)) && (((( !p1_l0) && ( !p1_l1)) || (p1_l0 && ( !p1_l1))) || ((p1_l1 && ( !p1_l0)) || (p1_l0 && p1_l1)))) && (((( !p0_l0) && ( !p0_l1)) && (((( !p0_l0) && ( !p0_l1)) || (p0_l0 && ( !p0_l1))) || ((p0_l1 && ( !p0_l0)) || (p0_l0 && p0_l1)))) && (((((((((num0 == 0) && (num1 == 0)) && (num0 <= max_num)) && (num1 <= max_num)) && ((num0 == max_num) || (num1 == max_num))) && (((num0 == 0) && (num1 == 0)) == (min_num == 0))) && ((num0 <= 0) || (min_num <= num0))) && ((num1 <= 0) || (min_num <= num1))) && ((num0 == min_num) || (num1 == min_num))))) && (((((( !(( !(_EL_U_218 || ( !((num0 == 0) || _EL_U_216)))) || (_EL_U_214 || ( !(((( !p0_l0) && ( !p0_l1)) || _EL_U_211) && (( !(( !p0_l0) && ( !p0_l1))) || _EL_U_210)))))) && ( !_J241)) && ( !_J247)) && ( !_J252)) && ( !_J258)) && ( !_J267)));
  while (__steps_to_fair >= 0 && __ok) {
    if (((((_J241 && _J247) && _J252) && _J258) && _J267)) {
      __steps_to_fair = __VERIFIER_nondet_int();
    } else {
      __steps_to_fair--;
    }
    _x_min_num = __VERIFIER_nondet_int();
    _x_num1 = __VERIFIER_nondet_int();
    _x_num0 = __VERIFIER_nondet_int();
    _x_max_num = __VERIFIER_nondet_int();
    _x_p0_l1 = __VERIFIER_nondet_bool();
    _x_p0_l0 = __VERIFIER_nondet_bool();
    _x_p1_l1 = __VERIFIER_nondet_bool();
    _x_p1_l0 = __VERIFIER_nondet_bool();
    _x__J267 = __VERIFIER_nondet_bool();
    _x__J258 = __VERIFIER_nondet_bool();
    _x__J252 = __VERIFIER_nondet_bool();
    _x__J247 = __VERIFIER_nondet_bool();
    _x__J241 = __VERIFIER_nondet_bool();
    _x__EL_U_210 = __VERIFIER_nondet_bool();
    _x__EL_U_211 = __VERIFIER_nondet_bool();
    _x__EL_U_214 = __VERIFIER_nondet_bool();
    _x__EL_U_216 = __VERIFIER_nondet_bool();
    _x__EL_U_218 = __VERIFIER_nondet_bool();
    _x_run0 = __VERIFIER_nondet_bool();

    __ok = (((((((((((( !_x_p1_l0) && ( !_x_p1_l1)) || (_x_p1_l0 && ( !_x_p1_l1))) || ((_x_p1_l1 && ( !_x_p1_l0)) || (_x_p1_l0 && _x_p1_l1))) && (run0 || (((p1_l0 == _x_p1_l0) && (p1_l1 == _x_p1_l1)) && (num1 == _x_num1)))) && (((_x_p1_l0 && ( !_x_p1_l1)) && ((_x_num1 + (-1 * max_num)) == 1)) || ( !(run0 && (( !p1_l0) && ( !p1_l1)))))) && (((num1 == _x_num1) && ((_x_p1_l0 && ( !_x_p1_l1)) || (_x_p1_l1 && ( !_x_p1_l0)))) || ( !(run0 && (p1_l0 && ( !p1_l1)))))) && (( !(run0 && (p1_l0 && ( !p1_l1)))) || ((_x_p1_l1 && ( !_x_p1_l0)) == ((num1 <= min_num) && ( !(num0 == min_num)))))) && (((num1 == _x_num1) && ((_x_p1_l1 && ( !_x_p1_l0)) || (_x_p1_l0 && _x_p1_l1))) || ( !(run0 && (p1_l1 && ( !p1_l0)))))) && (((( !_x_p1_l0) && ( !_x_p1_l1)) && (num1 == _x_num1)) || ( !(run0 && (p1_l0 && p1_l1))))) && ((((((((((( !_x_p0_l0) && ( !_x_p0_l1)) || (_x_p0_l0 && ( !_x_p0_l1))) || ((_x_p0_l1 && ( !_x_p0_l0)) || (_x_p0_l0 && _x_p0_l1))) && (( !run0) || (((p0_l0 == _x_p0_l0) && (p0_l1 == _x_p0_l1)) && (num0 == _x_num0)))) && (((_x_p0_l0 && ( !_x_p0_l1)) && ((_x_num0 + (-1 * max_num)) == 1)) || ( !(( !run0) && (( !p0_l0) && ( !p0_l1)))))) && (((num0 == _x_num0) && ((_x_p0_l0 && ( !_x_p0_l1)) || (_x_p0_l1 && ( !_x_p0_l0)))) || ( !(( !run0) && (p0_l0 && ( !p0_l1)))))) && (( !(( !run0) && (p0_l0 && ( !p0_l1)))) || ((_x_p0_l1 && ( !_x_p0_l0)) == (num0 <= min_num)))) && (((num0 == _x_num0) && ((_x_p0_l1 && ( !_x_p0_l0)) || (_x_p0_l0 && _x_p0_l1))) || ( !(( !run0) && (p0_l1 && ( !p0_l0)))))) && (((( !_x_p0_l0) && ( !_x_p0_l1)) && (num0 == _x_num0)) || ( !(( !run0) && (p0_l0 && p0_l1))))) && (((((((_x_num0 <= _x_max_num) && (_x_num1 <= _x_max_num)) && ((_x_num0 == _x_max_num) || (_x_num1 == _x_max_num))) && (((_x_num0 == 0) && (_x_num1 == 0)) == (_x_min_num == 0))) && ((_x_num0 <= 0) || (_x_min_num <= _x_num0))) && ((_x_num1 <= 0) || (_x_min_num <= _x_num1))) && ((_x_num0 == _x_min_num) || (_x_num1 == _x_min_num))))) && (((((((_EL_U_214 == (_x__EL_U_214 || ( !(((( !_x_p0_l0) && ( !_x_p0_l1)) || _x__EL_U_211) && (_x__EL_U_210 || ( !(( !_x_p0_l0) && ( !_x_p0_l1)))))))) && ((_EL_U_210 == (_x__EL_U_210 || ( !(( !_x_p0_l0) && ( !_x_p0_l1))))) && ((_EL_U_211 == ((( !_x_p0_l0) && ( !_x_p0_l1)) || _x__EL_U_211)) && ((_EL_U_216 == ((_x_num0 == 0) || _x__EL_U_216)) && (_EL_U_218 == (_x__EL_U_218 || ( !((_x_num0 == 0) || _x__EL_U_216)))))))) && (_x__J241 == (( !((((_J241 && _J247) && _J252) && _J258) && _J267)) && (((((_J241 && _J247) && _J252) && _J258) && _J267) || (((num0 == 0) || ( !((num0 == 0) || _EL_U_216))) || _J241))))) && (_x__J247 == (( !((((_J241 && _J247) && _J252) && _J258) && _J267)) && (((((_J241 && _J247) && _J252) && _J258) && _J267) || ((( !((num0 == 0) || _EL_U_216)) || ( !(_EL_U_218 || ( !((num0 == 0) || _EL_U_216))))) || _J247))))) && (_x__J252 == (( !((((_J241 && _J247) && _J252) && _J258) && _J267)) && (((((_J241 && _J247) && _J252) && _J258) && _J267) || (((( !p0_l0) && ( !p0_l1)) || ( !((( !p0_l0) && ( !p0_l1)) || _EL_U_211))) || _J252))))) && (_x__J258 == (( !((((_J241 && _J247) && _J252) && _J258) && _J267)) && (((((_J241 && _J247) && _J252) && _J258) && _J267) || ((( !(( !p0_l0) && ( !p0_l1))) || ( !(( !(( !p0_l0) && ( !p0_l1))) || _EL_U_210))) || _J258))))) && (_x__J267 == (( !((((_J241 && _J247) && _J252) && _J258) && _J267)) && (((((_J241 && _J247) && _J252) && _J258) && _J267) || ((( !(((( !p0_l0) && ( !p0_l1)) || _EL_U_211) && (( !(( !p0_l0) && ( !p0_l1))) || _EL_U_210))) || ( !(_EL_U_214 || ( !(((( !p0_l0) && ( !p0_l1)) || _EL_U_211) && (( !(( !p0_l0) && ( !p0_l1))) || _EL_U_210)))))) || _J267))))));
    min_num = _x_min_num;
    num1 = _x_num1;
    num0 = _x_num0;
    max_num = _x_max_num;
    p0_l1 = _x_p0_l1;
    p0_l0 = _x_p0_l0;
    p1_l1 = _x_p1_l1;
    p1_l0 = _x_p1_l0;
    _J267 = _x__J267;
    _J258 = _x__J258;
    _J252 = _x__J252;
    _J247 = _x__J247;
    _J241 = _x__J241;
    _EL_U_210 = _x__EL_U_210;
    _EL_U_211 = _x__EL_U_211;
    _EL_U_214 = _x__EL_U_214;
    _EL_U_216 = _x__EL_U_216;
    _EL_U_218 = _x__EL_U_218;
    run0 = _x_run0;

  }
}
