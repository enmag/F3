extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);
typedef enum {false, true} bool;
bool __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}

int main()
{
int sm1_l, _x_sm1_l;
int sm1_loop_len, _x_sm1_loop_len;
bool sm1_state, _x_sm1_state;
int sm0_l, _x_sm0_l;
int sm0_loop_len, _x_sm0_loop_len;
bool sm0_state, _x_sm0_state;
int semaphore, _x_semaphore;
bool _J218, _x__J218;
bool _J212, _x__J212;
bool _J206, _x__J206;
bool _J200, _x__J200;
bool _J194, _x__J194;
bool _J188, _x__J188;
bool _EL_U_150, _x__EL_U_150;
int run, _x_run;
bool _EL_U_152, _x__EL_U_152;
bool _EL_U_154, _x__EL_U_154;
bool _EL_U_156, _x__EL_U_156;
bool _EL_U_160, _x__EL_U_160;
bool _EL_U_162, _x__EL_U_162;

  int __steps_to_fair = __VERIFIER_nondet_int();
  sm1_l = __VERIFIER_nondet_int();
  sm1_loop_len = __VERIFIER_nondet_int();
  sm1_state = __VERIFIER_nondet_bool();
  sm0_l = __VERIFIER_nondet_int();
  sm0_loop_len = __VERIFIER_nondet_int();
  sm0_state = __VERIFIER_nondet_bool();
  semaphore = __VERIFIER_nondet_int();
  _J218 = __VERIFIER_nondet_bool();
  _J212 = __VERIFIER_nondet_bool();
  _J206 = __VERIFIER_nondet_bool();
  _J200 = __VERIFIER_nondet_bool();
  _J194 = __VERIFIER_nondet_bool();
  _J188 = __VERIFIER_nondet_bool();
  _EL_U_150 = __VERIFIER_nondet_bool();
  run = __VERIFIER_nondet_int();
  _EL_U_152 = __VERIFIER_nondet_bool();
  _EL_U_154 = __VERIFIER_nondet_bool();
  _EL_U_156 = __VERIFIER_nondet_bool();
  _EL_U_160 = __VERIFIER_nondet_bool();
  _EL_U_162 = __VERIFIER_nondet_bool();

  bool __ok = ((((semaphore == 0) && (sm0_state && (( !(sm0_loop_len <= 0)) && (sm0_l == 0)))) && (sm1_state && (( !(sm1_loop_len <= 0)) && (sm1_l == 0)))) && ((((((( !((_EL_U_162 || ( !((semaphore == 0) || _EL_U_160))) || ( !(( !(_EL_U_156 || ( !((run == 0) || _EL_U_154)))) && ( !(_EL_U_152 || ( !((run == 1) || _EL_U_150)))))))) && ( !_J188)) && ( !_J194)) && ( !_J200)) && ( !_J206)) && ( !_J212)) && ( !_J218)));
  while (__steps_to_fair >= 0 && __ok) {
    if ((((((_J188 && _J194) && _J200) && _J206) && _J212) && _J218)) {
      __steps_to_fair = __VERIFIER_nondet_int();
    } else {
      __steps_to_fair--;
    }
    _x_sm1_l = __VERIFIER_nondet_int();
    _x_sm1_loop_len = __VERIFIER_nondet_int();
    _x_sm1_state = __VERIFIER_nondet_bool();
    _x_sm0_l = __VERIFIER_nondet_int();
    _x_sm0_loop_len = __VERIFIER_nondet_int();
    _x_sm0_state = __VERIFIER_nondet_bool();
    _x_semaphore = __VERIFIER_nondet_int();
    _x__J218 = __VERIFIER_nondet_bool();
    _x__J212 = __VERIFIER_nondet_bool();
    _x__J206 = __VERIFIER_nondet_bool();
    _x__J200 = __VERIFIER_nondet_bool();
    _x__J194 = __VERIFIER_nondet_bool();
    _x__J188 = __VERIFIER_nondet_bool();
    _x__EL_U_150 = __VERIFIER_nondet_bool();
    _x_run = __VERIFIER_nondet_int();
    _x__EL_U_152 = __VERIFIER_nondet_bool();
    _x__EL_U_154 = __VERIFIER_nondet_bool();
    _x__EL_U_156 = __VERIFIER_nondet_bool();
    _x__EL_U_160 = __VERIFIER_nondet_bool();
    _x__EL_U_162 = __VERIFIER_nondet_bool();

    __ok = (((((_x_semaphore == 0) || ( !(semaphore == 2))) && ((((((((((sm0_l == 0) && ( !(_x_sm0_loop_len <= sm0_loop_len))) || ( !(_x_sm0_state && ( !sm0_state)))) && ((_x_sm0_state && ( !sm0_state)) || (sm0_loop_len == _x_sm0_loop_len))) && (( !sm0_state) || ((sm0_l + (-1 * _x_sm0_l)) == 1))) && (_x_sm0_state || ( !(sm0_state && ( !(sm0_loop_len <= sm0_l)))))) && (_x_sm0_state || ( !(((semaphore == 2) && (_x_semaphore == 0)) && ( !sm0_state))))) && ((sm0_state == _x_sm0_state) || ( !(( !(((semaphore == 2) && (_x_semaphore == 0)) && ( !sm0_state))) && ( !(run == 0)))))) && ((semaphore == _x_semaphore) || ( !((run == 0) && (sm0_state == _x_sm0_state))))) && (((semaphore + (-1 * _x_semaphore)) == -1) || ( !(( !_x_sm0_state) && ((run == 0) && sm0_state)))))) && ((((((((((sm1_l == 0) && ( !(_x_sm1_loop_len <= sm1_loop_len))) || ( !(_x_sm1_state && ( !sm1_state)))) && ((_x_sm1_state && ( !sm1_state)) || (sm1_loop_len == _x_sm1_loop_len))) && (( !sm1_state) || ((sm1_l + (-1 * _x_sm1_l)) == 1))) && (_x_sm1_state || ( !(sm1_state && ( !(sm1_loop_len <= sm1_l)))))) && (_x_sm1_state || ( !(((semaphore == 2) && (_x_semaphore == 0)) && ( !sm1_state))))) && ((sm1_state == _x_sm1_state) || ( !(( !(((semaphore == 2) && (_x_semaphore == 0)) && ( !sm1_state))) && ( !(run == 1)))))) && ((semaphore == _x_semaphore) || ( !((run == 1) && (sm1_state == _x_sm1_state))))) && (((semaphore + (-1 * _x_semaphore)) == -1) || ( !(( !_x_sm1_state) && ((run == 1) && sm1_state)))))) && ((((((((_EL_U_152 == (_x__EL_U_152 || ( !(_x__EL_U_150 || (_x_run == 1))))) && ((_EL_U_150 == (_x__EL_U_150 || (_x_run == 1))) && ((_EL_U_156 == (_x__EL_U_156 || ( !(_x__EL_U_154 || (_x_run == 0))))) && ((_EL_U_154 == (_x__EL_U_154 || (_x_run == 0))) && ((_EL_U_160 == ((_x_semaphore == 0) || _x__EL_U_160)) && (_EL_U_162 == (_x__EL_U_162 || ( !((_x_semaphore == 0) || _x__EL_U_160))))))))) && (_x__J188 == (( !(((((_J188 && _J194) && _J200) && _J206) && _J212) && _J218)) && ((((((_J188 && _J194) && _J200) && _J206) && _J212) && _J218) || (((semaphore == 0) || ( !((semaphore == 0) || _EL_U_160))) || _J188))))) && (_x__J194 == (( !(((((_J188 && _J194) && _J200) && _J206) && _J212) && _J218)) && ((((((_J188 && _J194) && _J200) && _J206) && _J212) && _J218) || ((( !((semaphore == 0) || _EL_U_160)) || ( !(_EL_U_162 || ( !((semaphore == 0) || _EL_U_160))))) || _J194))))) && (_x__J200 == (( !(((((_J188 && _J194) && _J200) && _J206) && _J212) && _J218)) && ((((((_J188 && _J194) && _J200) && _J206) && _J212) && _J218) || (((run == 0) || ( !((run == 0) || _EL_U_154))) || _J200))))) && (_x__J206 == (( !(((((_J188 && _J194) && _J200) && _J206) && _J212) && _J218)) && ((((((_J188 && _J194) && _J200) && _J206) && _J212) && _J218) || ((( !((run == 0) || _EL_U_154)) || ( !(_EL_U_156 || ( !((run == 0) || _EL_U_154))))) || _J206))))) && (_x__J212 == (( !(((((_J188 && _J194) && _J200) && _J206) && _J212) && _J218)) && ((((((_J188 && _J194) && _J200) && _J206) && _J212) && _J218) || (((run == 1) || ( !((run == 1) || _EL_U_150))) || _J212))))) && (_x__J218 == (( !(((((_J188 && _J194) && _J200) && _J206) && _J212) && _J218)) && ((((((_J188 && _J194) && _J200) && _J206) && _J212) && _J218) || ((( !((run == 1) || _EL_U_150)) || ( !(_EL_U_152 || ( !((run == 1) || _EL_U_150))))) || _J218))))));
    sm1_l = _x_sm1_l;
    sm1_loop_len = _x_sm1_loop_len;
    sm1_state = _x_sm1_state;
    sm0_l = _x_sm0_l;
    sm0_loop_len = _x_sm0_loop_len;
    sm0_state = _x_sm0_state;
    semaphore = _x_semaphore;
    _J218 = _x__J218;
    _J212 = _x__J212;
    _J206 = _x__J206;
    _J200 = _x__J200;
    _J194 = _x__J194;
    _J188 = _x__J188;
    _EL_U_150 = _x__EL_U_150;
    run = _x_run;
    _EL_U_152 = _x__EL_U_152;
    _EL_U_154 = _x__EL_U_154;
    _EL_U_156 = _x__EL_U_156;
    _EL_U_160 = _x__EL_U_160;
    _EL_U_162 = _x__EL_U_162;

  }
}
