extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);
typedef enum {false, true} bool;
bool __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}

int main()
{
int sm2_l, _x_sm2_l;
int sm2_loop_len, _x_sm2_loop_len;
bool sm2_state, _x_sm2_state;
int sm1_l, _x_sm1_l;
int sm1_loop_len, _x_sm1_loop_len;
bool sm1_state, _x_sm1_state;
int sm0_l, _x_sm0_l;
int sm0_loop_len, _x_sm0_loop_len;
bool sm0_state, _x_sm0_state;
int semaphore, _x_semaphore;
bool _J302, _x__J302;
bool _J296, _x__J296;
bool _J289, _x__J289;
bool _J283, _x__J283;
bool _J277, _x__J277;
bool _J271, _x__J271;
bool _J265, _x__J265;
bool _J259, _x__J259;
bool _EL_U_210, _x__EL_U_210;
int run, _x_run;
bool _EL_U_212, _x__EL_U_212;
bool _EL_U_214, _x__EL_U_214;
bool _EL_U_216, _x__EL_U_216;
bool _EL_U_218, _x__EL_U_218;
bool _EL_U_220, _x__EL_U_220;
bool _EL_U_225, _x__EL_U_225;
bool _EL_U_227, _x__EL_U_227;

  int __steps_to_fair = __VERIFIER_nondet_int();
  sm2_l = __VERIFIER_nondet_int();
  sm2_loop_len = __VERIFIER_nondet_int();
  sm2_state = __VERIFIER_nondet_bool();
  sm1_l = __VERIFIER_nondet_int();
  sm1_loop_len = __VERIFIER_nondet_int();
  sm1_state = __VERIFIER_nondet_bool();
  sm0_l = __VERIFIER_nondet_int();
  sm0_loop_len = __VERIFIER_nondet_int();
  sm0_state = __VERIFIER_nondet_bool();
  semaphore = __VERIFIER_nondet_int();
  _J302 = __VERIFIER_nondet_bool();
  _J296 = __VERIFIER_nondet_bool();
  _J289 = __VERIFIER_nondet_bool();
  _J283 = __VERIFIER_nondet_bool();
  _J277 = __VERIFIER_nondet_bool();
  _J271 = __VERIFIER_nondet_bool();
  _J265 = __VERIFIER_nondet_bool();
  _J259 = __VERIFIER_nondet_bool();
  _EL_U_210 = __VERIFIER_nondet_bool();
  run = __VERIFIER_nondet_int();
  _EL_U_212 = __VERIFIER_nondet_bool();
  _EL_U_214 = __VERIFIER_nondet_bool();
  _EL_U_216 = __VERIFIER_nondet_bool();
  _EL_U_218 = __VERIFIER_nondet_bool();
  _EL_U_220 = __VERIFIER_nondet_bool();
  _EL_U_225 = __VERIFIER_nondet_bool();
  _EL_U_227 = __VERIFIER_nondet_bool();

  bool __ok = (((((semaphore == 0) && (sm0_state && (( !(sm0_loop_len <= 0)) && (sm0_l == 0)))) && (sm1_state && (( !(sm1_loop_len <= 0)) && (sm1_l == 0)))) && (sm2_state && (( !(sm2_loop_len <= 0)) && (sm2_l == 0)))) && ((((((((( !((_EL_U_227 || ( !((semaphore == 0) || _EL_U_225))) || ( !((( !(_EL_U_220 || ( !((run == 0) || _EL_U_218)))) && ( !(_EL_U_216 || ( !((run == 1) || _EL_U_214))))) && ( !(_EL_U_212 || ( !((run == 2) || _EL_U_210)))))))) && ( !_J259)) && ( !_J265)) && ( !_J271)) && ( !_J277)) && ( !_J283)) && ( !_J289)) && ( !_J296)) && ( !_J302)));
  while (__steps_to_fair >= 0 && __ok) {
    if ((((((((_J259 && _J265) && _J271) && _J277) && _J283) && _J289) && _J296) && _J302)) {
      __steps_to_fair = __VERIFIER_nondet_int();
    } else {
      __steps_to_fair--;
    }
    _x_sm2_l = __VERIFIER_nondet_int();
    _x_sm2_loop_len = __VERIFIER_nondet_int();
    _x_sm2_state = __VERIFIER_nondet_bool();
    _x_sm1_l = __VERIFIER_nondet_int();
    _x_sm1_loop_len = __VERIFIER_nondet_int();
    _x_sm1_state = __VERIFIER_nondet_bool();
    _x_sm0_l = __VERIFIER_nondet_int();
    _x_sm0_loop_len = __VERIFIER_nondet_int();
    _x_sm0_state = __VERIFIER_nondet_bool();
    _x_semaphore = __VERIFIER_nondet_int();
    _x__J302 = __VERIFIER_nondet_bool();
    _x__J296 = __VERIFIER_nondet_bool();
    _x__J289 = __VERIFIER_nondet_bool();
    _x__J283 = __VERIFIER_nondet_bool();
    _x__J277 = __VERIFIER_nondet_bool();
    _x__J271 = __VERIFIER_nondet_bool();
    _x__J265 = __VERIFIER_nondet_bool();
    _x__J259 = __VERIFIER_nondet_bool();
    _x__EL_U_210 = __VERIFIER_nondet_bool();
    _x_run = __VERIFIER_nondet_int();
    _x__EL_U_212 = __VERIFIER_nondet_bool();
    _x__EL_U_214 = __VERIFIER_nondet_bool();
    _x__EL_U_216 = __VERIFIER_nondet_bool();
    _x__EL_U_218 = __VERIFIER_nondet_bool();
    _x__EL_U_220 = __VERIFIER_nondet_bool();
    _x__EL_U_225 = __VERIFIER_nondet_bool();
    _x__EL_U_227 = __VERIFIER_nondet_bool();

    __ok = ((((((_x_semaphore == 0) || ( !(semaphore == 3))) && ((((((((((sm0_l == 0) && ( !(_x_sm0_loop_len <= sm0_loop_len))) || ( !(_x_sm0_state && ( !sm0_state)))) && ((_x_sm0_state && ( !sm0_state)) || (sm0_loop_len == _x_sm0_loop_len))) && (( !sm0_state) || ((sm0_l + (-1 * _x_sm0_l)) == 1))) && (_x_sm0_state || ( !(sm0_state && ( !(sm0_loop_len <= sm0_l)))))) && (_x_sm0_state || ( !(((semaphore == 3) && (_x_semaphore == 0)) && ( !sm0_state))))) && ((sm0_state == _x_sm0_state) || ( !(( !(((semaphore == 3) && (_x_semaphore == 0)) && ( !sm0_state))) && ( !(run == 0)))))) && ((semaphore == _x_semaphore) || ( !((run == 0) && (sm0_state == _x_sm0_state))))) && (((semaphore + (-1 * _x_semaphore)) == -1) || ( !(( !_x_sm0_state) && ((run == 0) && sm0_state)))))) && ((((((((((sm1_l == 0) && ( !(_x_sm1_loop_len <= sm1_loop_len))) || ( !(_x_sm1_state && ( !sm1_state)))) && ((_x_sm1_state && ( !sm1_state)) || (sm1_loop_len == _x_sm1_loop_len))) && (( !sm1_state) || ((sm1_l + (-1 * _x_sm1_l)) == 1))) && (_x_sm1_state || ( !(sm1_state && ( !(sm1_loop_len <= sm1_l)))))) && (_x_sm1_state || ( !(((semaphore == 3) && (_x_semaphore == 0)) && ( !sm1_state))))) && ((sm1_state == _x_sm1_state) || ( !(( !(((semaphore == 3) && (_x_semaphore == 0)) && ( !sm1_state))) && ( !(run == 1)))))) && ((semaphore == _x_semaphore) || ( !((run == 1) && (sm1_state == _x_sm1_state))))) && (((semaphore + (-1 * _x_semaphore)) == -1) || ( !(( !_x_sm1_state) && ((run == 1) && sm1_state)))))) && ((((((((((sm2_l == 0) && ( !(_x_sm2_loop_len <= sm2_loop_len))) || ( !(_x_sm2_state && ( !sm2_state)))) && ((_x_sm2_state && ( !sm2_state)) || (sm2_loop_len == _x_sm2_loop_len))) && (( !sm2_state) || ((sm2_l + (-1 * _x_sm2_l)) == 1))) && (_x_sm2_state || ( !(sm2_state && ( !(sm2_loop_len <= sm2_l)))))) && (_x_sm2_state || ( !(((semaphore == 3) && (_x_semaphore == 0)) && ( !sm2_state))))) && ((sm2_state == _x_sm2_state) || ( !(( !(((semaphore == 3) && (_x_semaphore == 0)) && ( !sm2_state))) && ( !(run == 2)))))) && ((semaphore == _x_semaphore) || ( !((run == 2) && (sm2_state == _x_sm2_state))))) && (((semaphore + (-1 * _x_semaphore)) == -1) || ( !(( !_x_sm2_state) && ((run == 2) && sm2_state)))))) && ((((((((((_EL_U_212 == (_x__EL_U_212 || ( !(_x__EL_U_210 || (_x_run == 2))))) && ((_EL_U_210 == (_x__EL_U_210 || (_x_run == 2))) && ((_EL_U_216 == (_x__EL_U_216 || ( !(_x__EL_U_214 || (_x_run == 1))))) && ((_EL_U_214 == (_x__EL_U_214 || (_x_run == 1))) && ((_EL_U_220 == (_x__EL_U_220 || ( !(_x__EL_U_218 || (_x_run == 0))))) && ((_EL_U_218 == (_x__EL_U_218 || (_x_run == 0))) && ((_EL_U_225 == ((_x_semaphore == 0) || _x__EL_U_225)) && (_EL_U_227 == (_x__EL_U_227 || ( !((_x_semaphore == 0) || _x__EL_U_225))))))))))) && (_x__J259 == (( !(((((((_J259 && _J265) && _J271) && _J277) && _J283) && _J289) && _J296) && _J302)) && ((((((((_J259 && _J265) && _J271) && _J277) && _J283) && _J289) && _J296) && _J302) || (((semaphore == 0) || ( !((semaphore == 0) || _EL_U_225))) || _J259))))) && (_x__J265 == (( !(((((((_J259 && _J265) && _J271) && _J277) && _J283) && _J289) && _J296) && _J302)) && ((((((((_J259 && _J265) && _J271) && _J277) && _J283) && _J289) && _J296) && _J302) || ((( !((semaphore == 0) || _EL_U_225)) || ( !(_EL_U_227 || ( !((semaphore == 0) || _EL_U_225))))) || _J265))))) && (_x__J271 == (( !(((((((_J259 && _J265) && _J271) && _J277) && _J283) && _J289) && _J296) && _J302)) && ((((((((_J259 && _J265) && _J271) && _J277) && _J283) && _J289) && _J296) && _J302) || (((run == 0) || ( !((run == 0) || _EL_U_218))) || _J271))))) && (_x__J277 == (( !(((((((_J259 && _J265) && _J271) && _J277) && _J283) && _J289) && _J296) && _J302)) && ((((((((_J259 && _J265) && _J271) && _J277) && _J283) && _J289) && _J296) && _J302) || ((( !((run == 0) || _EL_U_218)) || ( !(_EL_U_220 || ( !((run == 0) || _EL_U_218))))) || _J277))))) && (_x__J283 == (( !(((((((_J259 && _J265) && _J271) && _J277) && _J283) && _J289) && _J296) && _J302)) && ((((((((_J259 && _J265) && _J271) && _J277) && _J283) && _J289) && _J296) && _J302) || (((run == 1) || ( !((run == 1) || _EL_U_214))) || _J283))))) && (_x__J289 == (( !(((((((_J259 && _J265) && _J271) && _J277) && _J283) && _J289) && _J296) && _J302)) && ((((((((_J259 && _J265) && _J271) && _J277) && _J283) && _J289) && _J296) && _J302) || ((( !((run == 1) || _EL_U_214)) || ( !(_EL_U_216 || ( !((run == 1) || _EL_U_214))))) || _J289))))) && (_x__J296 == (( !(((((((_J259 && _J265) && _J271) && _J277) && _J283) && _J289) && _J296) && _J302)) && ((((((((_J259 && _J265) && _J271) && _J277) && _J283) && _J289) && _J296) && _J302) || (((run == 2) || ( !((run == 2) || _EL_U_210))) || _J296))))) && (_x__J302 == (( !(((((((_J259 && _J265) && _J271) && _J277) && _J283) && _J289) && _J296) && _J302)) && ((((((((_J259 && _J265) && _J271) && _J277) && _J283) && _J289) && _J296) && _J302) || ((( !((run == 2) || _EL_U_210)) || ( !(_EL_U_212 || ( !((run == 2) || _EL_U_210))))) || _J302))))));
    sm2_l = _x_sm2_l;
    sm2_loop_len = _x_sm2_loop_len;
    sm2_state = _x_sm2_state;
    sm1_l = _x_sm1_l;
    sm1_loop_len = _x_sm1_loop_len;
    sm1_state = _x_sm1_state;
    sm0_l = _x_sm0_l;
    sm0_loop_len = _x_sm0_loop_len;
    sm0_state = _x_sm0_state;
    semaphore = _x_semaphore;
    _J302 = _x__J302;
    _J296 = _x__J296;
    _J289 = _x__J289;
    _J283 = _x__J283;
    _J277 = _x__J277;
    _J271 = _x__J271;
    _J265 = _x__J265;
    _J259 = _x__J259;
    _EL_U_210 = _x__EL_U_210;
    run = _x_run;
    _EL_U_212 = _x__EL_U_212;
    _EL_U_214 = _x__EL_U_214;
    _EL_U_216 = _x__EL_U_216;
    _EL_U_218 = _x__EL_U_218;
    _EL_U_220 = _x__EL_U_220;
    _EL_U_225 = _x__EL_U_225;
    _EL_U_227 = _x__EL_U_227;

  }
}
