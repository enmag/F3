//@ ltl invariant negative: ( (! ([] (<> AP((semaphore == 0))))) || (! ( ( ( ( ( ([] (<> AP((run == 0)))) && ([] (<> AP((run == 1))))) && ([] (<> AP((run == 2))))) && ([] (<> AP((run == 3))))) && ([] (<> AP((run == 4))))) && ([] (<> AP((run == 5)))))));

extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);

char __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}


int sm5_loop_len, _x_sm5_loop_len;
char sm5_state, _x_sm5_state;
int sm4_loop_len, _x_sm4_loop_len;
char sm4_state, _x_sm4_state;
int run, _x_run;
int semaphore, _x_semaphore;
int sm1_loop_len, _x_sm1_loop_len;
int sm3_loop_len, _x_sm3_loop_len;
int sm3_l, _x_sm3_l;
char sm1_state, _x_sm1_state;
int sm1_l, _x_sm1_l;
int sm5_l, _x_sm5_l;
char sm3_state, _x_sm3_state;
int sm4_l, _x_sm4_l;
char sm0_state, _x_sm0_state;
char sm2_state, _x_sm2_state;
int sm0_loop_len, _x_sm0_loop_len;
int sm2_loop_len, _x_sm2_loop_len;
int sm0_l, _x_sm0_l;
int sm2_l, _x_sm2_l;

int main()
{
  sm5_loop_len = __VERIFIER_nondet_int();
  sm5_state = __VERIFIER_nondet_bool();
  sm4_loop_len = __VERIFIER_nondet_int();
  sm4_state = __VERIFIER_nondet_bool();
  run = __VERIFIER_nondet_int();
  semaphore = __VERIFIER_nondet_int();
  sm1_loop_len = __VERIFIER_nondet_int();
  sm3_loop_len = __VERIFIER_nondet_int();
  sm3_l = __VERIFIER_nondet_int();
  sm1_state = __VERIFIER_nondet_bool();
  sm1_l = __VERIFIER_nondet_int();
  sm5_l = __VERIFIER_nondet_int();
  sm3_state = __VERIFIER_nondet_bool();
  sm4_l = __VERIFIER_nondet_int();
  sm0_state = __VERIFIER_nondet_bool();
  sm2_state = __VERIFIER_nondet_bool();
  sm0_loop_len = __VERIFIER_nondet_int();
  sm2_loop_len = __VERIFIER_nondet_int();
  sm0_l = __VERIFIER_nondet_int();
  sm2_l = __VERIFIER_nondet_int();

  int __ok = (((((((semaphore == 0) && ((sm0_state != 0) && (( !(sm0_loop_len <= 0)) && (sm0_l == 0)))) && ((sm1_state != 0) && (( !(sm1_loop_len <= 0)) && (sm1_l == 0)))) && ((sm2_state != 0) && (( !(sm2_loop_len <= 0)) && (sm2_l == 0)))) && ((sm3_state != 0) && (( !(sm3_loop_len <= 0)) && (sm3_l == 0)))) && ((sm4_state != 0) && (( !(sm4_loop_len <= 0)) && (sm4_l == 0)))) && ((sm5_state != 0) && (( !(sm5_loop_len <= 0)) && (sm5_l == 0))));
  while (__ok) {
    _x_sm5_loop_len = __VERIFIER_nondet_int();
    _x_sm5_state = __VERIFIER_nondet_bool();
    _x_sm4_loop_len = __VERIFIER_nondet_int();
    _x_sm4_state = __VERIFIER_nondet_bool();
    _x_run = __VERIFIER_nondet_int();
    _x_semaphore = __VERIFIER_nondet_int();
    _x_sm1_loop_len = __VERIFIER_nondet_int();
    _x_sm3_loop_len = __VERIFIER_nondet_int();
    _x_sm3_l = __VERIFIER_nondet_int();
    _x_sm1_state = __VERIFIER_nondet_bool();
    _x_sm1_l = __VERIFIER_nondet_int();
    _x_sm5_l = __VERIFIER_nondet_int();
    _x_sm3_state = __VERIFIER_nondet_bool();
    _x_sm4_l = __VERIFIER_nondet_int();
    _x_sm0_state = __VERIFIER_nondet_bool();
    _x_sm2_state = __VERIFIER_nondet_bool();
    _x_sm0_loop_len = __VERIFIER_nondet_int();
    _x_sm2_loop_len = __VERIFIER_nondet_int();
    _x_sm0_l = __VERIFIER_nondet_int();
    _x_sm2_l = __VERIFIER_nondet_int();

    __ok = ((((((((_x_semaphore == 0) || ( !(semaphore == 6))) && ((((((((((sm0_l == 0) && ( !(_x_sm0_loop_len <= sm0_loop_len))) || ( !((_x_sm0_state != 0) && ( !(sm0_state != 0))))) && (((_x_sm0_state != 0) && ( !(sm0_state != 0))) || (sm0_loop_len == _x_sm0_loop_len))) && (( !(sm0_state != 0)) || ((sm0_l + (-1 * _x_sm0_l)) == 1))) && ((_x_sm0_state != 0) || ( !((sm0_state != 0) && ( !(sm0_loop_len <= sm0_l)))))) && ((_x_sm0_state != 0) || ( !(((semaphore == 6) && (_x_semaphore == 0)) && ( !(sm0_state != 0)))))) && (((sm0_state != 0) == (_x_sm0_state != 0)) || ( !(( !(((semaphore == 6) && (_x_semaphore == 0)) && ( !(sm0_state != 0)))) && ( !(run == 0)))))) && ((semaphore == _x_semaphore) || ( !((run == 0) && ((sm0_state != 0) == (_x_sm0_state != 0)))))) && (((semaphore + (-1 * _x_semaphore)) == -1) || ( !(( !(_x_sm0_state != 0)) && ((run == 0) && (sm0_state != 0))))))) && ((((((((((sm1_l == 0) && ( !(_x_sm1_loop_len <= sm1_loop_len))) || ( !((_x_sm1_state != 0) && ( !(sm1_state != 0))))) && (((_x_sm1_state != 0) && ( !(sm1_state != 0))) || (sm1_loop_len == _x_sm1_loop_len))) && (( !(sm1_state != 0)) || ((sm1_l + (-1 * _x_sm1_l)) == 1))) && ((_x_sm1_state != 0) || ( !((sm1_state != 0) && ( !(sm1_loop_len <= sm1_l)))))) && ((_x_sm1_state != 0) || ( !(((semaphore == 6) && (_x_semaphore == 0)) && ( !(sm1_state != 0)))))) && (((sm1_state != 0) == (_x_sm1_state != 0)) || ( !(( !(((semaphore == 6) && (_x_semaphore == 0)) && ( !(sm1_state != 0)))) && ( !(run == 1)))))) && ((semaphore == _x_semaphore) || ( !((run == 1) && ((sm1_state != 0) == (_x_sm1_state != 0)))))) && (((semaphore + (-1 * _x_semaphore)) == -1) || ( !(( !(_x_sm1_state != 0)) && ((run == 1) && (sm1_state != 0))))))) && ((((((((((sm2_l == 0) && ( !(_x_sm2_loop_len <= sm2_loop_len))) || ( !((_x_sm2_state != 0) && ( !(sm2_state != 0))))) && (((_x_sm2_state != 0) && ( !(sm2_state != 0))) || (sm2_loop_len == _x_sm2_loop_len))) && (( !(sm2_state != 0)) || ((sm2_l + (-1 * _x_sm2_l)) == 1))) && ((_x_sm2_state != 0) || ( !((sm2_state != 0) && ( !(sm2_loop_len <= sm2_l)))))) && ((_x_sm2_state != 0) || ( !(((semaphore == 6) && (_x_semaphore == 0)) && ( !(sm2_state != 0)))))) && (((sm2_state != 0) == (_x_sm2_state != 0)) || ( !(( !(((semaphore == 6) && (_x_semaphore == 0)) && ( !(sm2_state != 0)))) && ( !(run == 2)))))) && ((semaphore == _x_semaphore) || ( !((run == 2) && ((sm2_state != 0) == (_x_sm2_state != 0)))))) && (((semaphore + (-1 * _x_semaphore)) == -1) || ( !(( !(_x_sm2_state != 0)) && ((run == 2) && (sm2_state != 0))))))) && ((((((((((sm3_l == 0) && ( !(_x_sm3_loop_len <= sm3_loop_len))) || ( !((_x_sm3_state != 0) && ( !(sm3_state != 0))))) && (((_x_sm3_state != 0) && ( !(sm3_state != 0))) || (sm3_loop_len == _x_sm3_loop_len))) && (( !(sm3_state != 0)) || ((sm3_l + (-1 * _x_sm3_l)) == 1))) && ((_x_sm3_state != 0) || ( !((sm3_state != 0) && ( !(sm3_loop_len <= sm3_l)))))) && ((_x_sm3_state != 0) || ( !(((semaphore == 6) && (_x_semaphore == 0)) && ( !(sm3_state != 0)))))) && (((sm3_state != 0) == (_x_sm3_state != 0)) || ( !(( !(((semaphore == 6) && (_x_semaphore == 0)) && ( !(sm3_state != 0)))) && ( !(run == 3)))))) && ((semaphore == _x_semaphore) || ( !((run == 3) && ((sm3_state != 0) == (_x_sm3_state != 0)))))) && (((semaphore + (-1 * _x_semaphore)) == -1) || ( !(( !(_x_sm3_state != 0)) && ((run == 3) && (sm3_state != 0))))))) && ((((((((((sm4_l == 0) && ( !(_x_sm4_loop_len <= sm4_loop_len))) || ( !((_x_sm4_state != 0) && ( !(sm4_state != 0))))) && (((_x_sm4_state != 0) && ( !(sm4_state != 0))) || (sm4_loop_len == _x_sm4_loop_len))) && (( !(sm4_state != 0)) || ((sm4_l + (-1 * _x_sm4_l)) == 1))) && ((_x_sm4_state != 0) || ( !((sm4_state != 0) && ( !(sm4_loop_len <= sm4_l)))))) && ((_x_sm4_state != 0) || ( !(((semaphore == 6) && (_x_semaphore == 0)) && ( !(sm4_state != 0)))))) && (((sm4_state != 0) == (_x_sm4_state != 0)) || ( !(( !(((semaphore == 6) && (_x_semaphore == 0)) && ( !(sm4_state != 0)))) && ( !(run == 4)))))) && ((semaphore == _x_semaphore) || ( !((run == 4) && ((sm4_state != 0) == (_x_sm4_state != 0)))))) && (((semaphore + (-1 * _x_semaphore)) == -1) || ( !(( !(_x_sm4_state != 0)) && ((run == 4) && (sm4_state != 0))))))) && ((((((((((sm5_l == 0) && ( !(_x_sm5_loop_len <= sm5_loop_len))) || ( !((_x_sm5_state != 0) && ( !(sm5_state != 0))))) && (((_x_sm5_state != 0) && ( !(sm5_state != 0))) || (sm5_loop_len == _x_sm5_loop_len))) && (( !(sm5_state != 0)) || ((sm5_l + (-1 * _x_sm5_l)) == 1))) && ((_x_sm5_state != 0) || ( !((sm5_state != 0) && ( !(sm5_loop_len <= sm5_l)))))) && ((_x_sm5_state != 0) || ( !(((semaphore == 6) && (_x_semaphore == 0)) && ( !(sm5_state != 0)))))) && (((sm5_state != 0) == (_x_sm5_state != 0)) || ( !(( !(((semaphore == 6) && (_x_semaphore == 0)) && ( !(sm5_state != 0)))) && ( !(run == 5)))))) && ((semaphore == _x_semaphore) || ( !((run == 5) && ((sm5_state != 0) == (_x_sm5_state != 0)))))) && (((semaphore + (-1 * _x_semaphore)) == -1) || ( !(( !(_x_sm5_state != 0)) && ((run == 5) && (sm5_state != 0)))))));
    sm5_loop_len = _x_sm5_loop_len;
    sm5_state = _x_sm5_state;
    sm4_loop_len = _x_sm4_loop_len;
    sm4_state = _x_sm4_state;
    run = _x_run;
    semaphore = _x_semaphore;
    sm1_loop_len = _x_sm1_loop_len;
    sm3_loop_len = _x_sm3_loop_len;
    sm3_l = _x_sm3_l;
    sm1_state = _x_sm1_state;
    sm1_l = _x_sm1_l;
    sm5_l = _x_sm5_l;
    sm3_state = _x_sm3_state;
    sm4_l = _x_sm4_l;
    sm0_state = _x_sm0_state;
    sm2_state = _x_sm2_state;
    sm0_loop_len = _x_sm0_loop_len;
    sm2_loop_len = _x_sm2_loop_len;
    sm0_l = _x_sm0_l;
    sm2_l = _x_sm2_l;

  }
}
