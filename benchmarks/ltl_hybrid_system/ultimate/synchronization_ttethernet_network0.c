//@ ltl invariant negative: ( (<> ([] (! ( ( ( ( AP(((cm0_cm + (cm1_cm - (2.0 * sm0_sm))) == 0.0)) && AP(((cm0_cm + (cm1_cm - (2.0 * sm1_sm))) == 0.0))) && AP(((cm0_cm + (cm1_cm - (2.0 * sm2_sm))) == 0.0))) && AP(((cm0_cm + (cm1_cm - (2.0 * sm3_sm))) == 0.0))) && AP(((cm0_cm + (cm1_cm - (2.0 * sm4_sm))) == 0.0)))))) || (! ([] (<> AP((1.0 <= _diverge_delta))))));

extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);

char __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}


float sm4_sm, _x_sm4_sm;
int sm4_mode, _x_sm4_mode;
float sm3_sm, _x_sm3_sm;
int sm3_mode, _x_sm3_mode;
float delta, _x_delta;
int cm0_mode, _x_cm0_mode;
float _diverge_delta, _x__diverge_delta;
float cm0_cm, _x_cm0_cm;
float cm0_x, _x_cm0_x;
int cm1_mode, _x_cm1_mode;
float cm1_cm, _x_cm1_cm;
float cm1_x, _x_cm1_x;
int sm0_mode, _x_sm0_mode;
float sm0_sm, _x_sm0_sm;
int sm1_mode, _x_sm1_mode;
float sm1_sm, _x_sm1_sm;
int sm2_mode, _x_sm2_mode;
float sm2_sm, _x_sm2_sm;

int main()
{
  sm4_sm = __VERIFIER_nondet_float();
  sm4_mode = __VERIFIER_nondet_int();
  sm3_sm = __VERIFIER_nondet_float();
  sm3_mode = __VERIFIER_nondet_int();
  delta = __VERIFIER_nondet_float();
  cm0_mode = __VERIFIER_nondet_int();
  _diverge_delta = __VERIFIER_nondet_float();
  cm0_cm = __VERIFIER_nondet_float();
  cm0_x = __VERIFIER_nondet_float();
  cm1_mode = __VERIFIER_nondet_int();
  cm1_cm = __VERIFIER_nondet_float();
  cm1_x = __VERIFIER_nondet_float();
  sm0_mode = __VERIFIER_nondet_int();
  sm0_sm = __VERIFIER_nondet_float();
  sm1_mode = __VERIFIER_nondet_int();
  sm1_sm = __VERIFIER_nondet_float();
  sm2_mode = __VERIFIER_nondet_int();
  sm2_sm = __VERIFIER_nondet_float();

  int __ok = (((((((((0.0 <= delta) && ((((cm0_mode == 0) && (cm0_x == 0.0)) && (cm0_cm == 0.0)) && (((cm0_mode == 0) || ((cm0_x == 0.0) && (delta == 0.0))) && (( !(cm0_mode == 0)) || (cm0_x <= 2.0))))) && ((((cm1_mode == 0) && (cm1_x == 0.0)) && (cm1_cm == 0.0)) && (((cm1_mode == 0) || ((delta == 0.0) && (cm1_x == 0.0))) && (( !(cm1_mode == 0)) || (cm1_x <= 2.0))))) && ((sm0_mode == 0) && (sm0_sm == 0.0))) && ((sm1_mode == 0) && (sm1_sm == 0.0))) && ((sm2_mode == 0) && (sm2_sm == 0.0))) && ((sm3_mode == 0) && (sm3_sm == 0.0))) && ((sm4_mode == 0) && (sm4_sm == 0.0))) && (delta == _diverge_delta));
  while (__ok) {
    _x_sm4_sm = __VERIFIER_nondet_float();
    _x_sm4_mode = __VERIFIER_nondet_int();
    _x_sm3_sm = __VERIFIER_nondet_float();
    _x_sm3_mode = __VERIFIER_nondet_int();
    _x_delta = __VERIFIER_nondet_float();
    _x_cm0_mode = __VERIFIER_nondet_int();
    _x__diverge_delta = __VERIFIER_nondet_float();
    _x_cm0_cm = __VERIFIER_nondet_float();
    _x_cm0_x = __VERIFIER_nondet_float();
    _x_cm1_mode = __VERIFIER_nondet_int();
    _x_cm1_cm = __VERIFIER_nondet_float();
    _x_cm1_x = __VERIFIER_nondet_float();
    _x_sm0_mode = __VERIFIER_nondet_int();
    _x_sm0_sm = __VERIFIER_nondet_float();
    _x_sm1_mode = __VERIFIER_nondet_int();
    _x_sm1_sm = __VERIFIER_nondet_float();
    _x_sm2_mode = __VERIFIER_nondet_int();
    _x_sm2_sm = __VERIFIER_nondet_float();

    __ok = (((((((((((((((((((cm0_cm + (cm1_cm + (-2.0 * _x_sm0_sm))) == 0.0) || ( !((sm0_mode == 2) && (_x_sm0_mode == 3)))) && (((cm0_cm + (cm1_cm + (-2.0 * _x_sm1_sm))) == 0.0) || ( !((sm1_mode == 2) && (_x_sm1_mode == 3))))) && (((cm0_cm + (cm1_cm + (-2.0 * _x_sm2_sm))) == 0.0) || ( !((sm2_mode == 2) && (_x_sm2_mode == 3))))) && (((cm0_cm + (cm1_cm + (-2.0 * _x_sm3_sm))) == 0.0) || ( !((sm3_mode == 2) && (_x_sm3_mode == 3))))) && (((cm0_cm + (cm1_cm + (-2.0 * _x_sm4_sm))) == 0.0) || ( !((sm4_mode == 2) && (_x_sm4_mode == 3))))) && (((((5.0 * _x_cm0_cm) + ((-1.0 * sm0_sm) + ((-1.0 * sm1_sm) + ((-1.0 * sm2_sm) + ((-1.0 * sm3_sm) + (-1.0 * sm4_sm)))))) == 0.0) || ( !((cm0_mode == 1) && (_x_cm0_mode == 2)))) && ((((5.0 * _x_cm1_cm) + ((-1.0 * sm0_sm) + ((-1.0 * sm1_sm) + ((-1.0 * sm2_sm) + ((-1.0 * sm3_sm) + (-1.0 * sm4_sm)))))) == 0.0) || ( !((cm1_mode == 1) && (_x_cm1_mode == 2)))))) && ((((((((((cm0_mode == 0) && (_x_cm0_mode == 1)) == ((sm0_mode == 0) && (_x_sm0_mode == 1))) && (((cm0_mode == 1) && (_x_cm0_mode == 2)) == ((sm0_mode == 1) && (_x_sm0_mode == 2)))) && (((sm0_mode == 2) && (_x_sm0_mode == 3)) == ((cm0_mode == 2) && (_x_cm0_mode == 3)))) && (((cm0_mode == 3) && (_x_cm0_mode == 0)) == ((sm0_mode == 3) && (_x_sm0_mode == 0)))) && ((((((cm0_mode == 0) && (_x_cm0_mode == 1)) == ((sm1_mode == 0) && (_x_sm1_mode == 1))) && (((cm0_mode == 1) && (_x_cm0_mode == 2)) == ((sm1_mode == 1) && (_x_sm1_mode == 2)))) && (((sm1_mode == 2) && (_x_sm1_mode == 3)) == ((cm0_mode == 2) && (_x_cm0_mode == 3)))) && (((cm0_mode == 3) && (_x_cm0_mode == 0)) == ((sm1_mode == 3) && (_x_sm1_mode == 0))))) && ((((((cm0_mode == 0) && (_x_cm0_mode == 1)) == ((sm2_mode == 0) && (_x_sm2_mode == 1))) && (((cm0_mode == 1) && (_x_cm0_mode == 2)) == ((sm2_mode == 1) && (_x_sm2_mode == 2)))) && (((sm2_mode == 2) && (_x_sm2_mode == 3)) == ((cm0_mode == 2) && (_x_cm0_mode == 3)))) && (((cm0_mode == 3) && (_x_cm0_mode == 0)) == ((sm2_mode == 3) && (_x_sm2_mode == 0))))) && ((((((cm0_mode == 0) && (_x_cm0_mode == 1)) == ((sm3_mode == 0) && (_x_sm3_mode == 1))) && (((cm0_mode == 1) && (_x_cm0_mode == 2)) == ((sm3_mode == 1) && (_x_sm3_mode == 2)))) && (((sm3_mode == 2) && (_x_sm3_mode == 3)) == ((cm0_mode == 2) && (_x_cm0_mode == 3)))) && (((cm0_mode == 3) && (_x_cm0_mode == 0)) == ((sm3_mode == 3) && (_x_sm3_mode == 0))))) && ((((((cm0_mode == 0) && (_x_cm0_mode == 1)) == ((sm4_mode == 0) && (_x_sm4_mode == 1))) && (((cm0_mode == 1) && (_x_cm0_mode == 2)) == ((sm4_mode == 1) && (_x_sm4_mode == 2)))) && (((sm4_mode == 2) && (_x_sm4_mode == 3)) == ((cm0_mode == 2) && (_x_cm0_mode == 3)))) && (((cm0_mode == 3) && (_x_cm0_mode == 0)) == ((sm4_mode == 3) && (_x_sm4_mode == 0)))))) && ((((((((((sm0_mode == 0) && (_x_sm0_mode == 1)) == ((cm1_mode == 0) && (_x_cm1_mode == 1))) && (((cm1_mode == 1) && (_x_cm1_mode == 2)) == ((sm0_mode == 1) && (_x_sm0_mode == 2)))) && (((sm0_mode == 2) && (_x_sm0_mode == 3)) == ((cm1_mode == 2) && (_x_cm1_mode == 3)))) && (((sm0_mode == 3) && (_x_sm0_mode == 0)) == ((cm1_mode == 3) && (_x_cm1_mode == 0)))) && ((((((sm1_mode == 0) && (_x_sm1_mode == 1)) == ((cm1_mode == 0) && (_x_cm1_mode == 1))) && (((cm1_mode == 1) && (_x_cm1_mode == 2)) == ((sm1_mode == 1) && (_x_sm1_mode == 2)))) && (((sm1_mode == 2) && (_x_sm1_mode == 3)) == ((cm1_mode == 2) && (_x_cm1_mode == 3)))) && (((sm1_mode == 3) && (_x_sm1_mode == 0)) == ((cm1_mode == 3) && (_x_cm1_mode == 0))))) && ((((((sm2_mode == 0) && (_x_sm2_mode == 1)) == ((cm1_mode == 0) && (_x_cm1_mode == 1))) && (((cm1_mode == 1) && (_x_cm1_mode == 2)) == ((sm2_mode == 1) && (_x_sm2_mode == 2)))) && (((sm2_mode == 2) && (_x_sm2_mode == 3)) == ((cm1_mode == 2) && (_x_cm1_mode == 3)))) && (((sm2_mode == 3) && (_x_sm2_mode == 0)) == ((cm1_mode == 3) && (_x_cm1_mode == 0))))) && ((((((sm3_mode == 0) && (_x_sm3_mode == 1)) == ((cm1_mode == 0) && (_x_cm1_mode == 1))) && (((cm1_mode == 1) && (_x_cm1_mode == 2)) == ((sm3_mode == 1) && (_x_sm3_mode == 2)))) && (((sm3_mode == 2) && (_x_sm3_mode == 3)) == ((cm1_mode == 2) && (_x_cm1_mode == 3)))) && (((sm3_mode == 3) && (_x_sm3_mode == 0)) == ((cm1_mode == 3) && (_x_cm1_mode == 0))))) && ((((((sm4_mode == 0) && (_x_sm4_mode == 1)) == ((cm1_mode == 0) && (_x_cm1_mode == 1))) && (((cm1_mode == 1) && (_x_cm1_mode == 2)) == ((sm4_mode == 1) && (_x_sm4_mode == 2)))) && (((sm4_mode == 2) && (_x_sm4_mode == 3)) == ((cm1_mode == 2) && (_x_cm1_mode == 3)))) && (((sm4_mode == 3) && (_x_sm4_mode == 0)) == ((cm1_mode == 3) && (_x_cm1_mode == 0)))))) && (0.0 <= _x_delta)) && (((((((((delta <= 0.0) || (((delta + (cm0_x + (-1.0 * _x_cm0_x))) == 0.0) && (cm0_mode == _x_cm0_mode))) && ((_x_cm0_mode == 1) || ( !((cm0_mode == 0) && (delta == 0.0))))) && ((_x_cm0_mode == 2) || ( !((cm0_mode == 1) && (delta == 0.0))))) && ((_x_cm0_mode == 3) || ( !((cm0_mode == 2) && (delta == 0.0))))) && ((_x_cm0_mode == 0) || ( !((cm0_mode == 3) && (delta == 0.0))))) && (((2.0 <= cm0_x) && (_x_cm0_x == 0.0)) || ( !((cm0_mode == 0) && (_x_cm0_mode == 1))))) && (((cm0_mode == 1) && (_x_cm0_mode == 2)) || (cm0_cm == _x_cm0_cm))) && (((_x_cm0_mode == 0) || ((_x_cm0_x == 0.0) && (_x_delta == 0.0))) && (( !(_x_cm0_mode == 0)) || (_x_cm0_x <= 2.0))))) && (((((((((delta <= 0.0) || (((delta + (cm1_x + (-1.0 * _x_cm1_x))) == 0.0) && (cm1_mode == _x_cm1_mode))) && ((_x_cm1_mode == 1) || ( !((cm1_mode == 0) && (delta == 0.0))))) && ((_x_cm1_mode == 2) || ( !((cm1_mode == 1) && (delta == 0.0))))) && ((_x_cm1_mode == 3) || ( !((cm1_mode == 2) && (delta == 0.0))))) && ((_x_cm1_mode == 0) || ( !((cm1_mode == 3) && (delta == 0.0))))) && (((2.0 <= cm1_x) && (_x_cm1_x == 0.0)) || ( !((cm1_mode == 0) && (_x_cm1_mode == 1))))) && (((cm1_mode == 1) && (_x_cm1_mode == 2)) || (cm1_cm == _x_cm1_cm))) && (((_x_cm1_mode == 0) || ((_x_delta == 0.0) && (_x_cm1_x == 0.0))) && (( !(_x_cm1_mode == 0)) || (_x_cm1_x <= 2.0))))) && ((((((((delta <= 0.0) || (((delta + (sm0_sm + (-1.0 * _x_sm0_sm))) == 0.0) && (sm0_mode == _x_sm0_mode))) && ((_x_sm0_mode == 1) || ( !((sm0_mode == 0) && (delta == 0.0))))) && ((_x_sm0_mode == 2) || ( !((sm0_mode == 1) && (delta == 0.0))))) && ((_x_sm0_mode == 3) || ( !((sm0_mode == 2) && (delta == 0.0))))) && ((_x_sm0_mode == 0) || ( !((sm0_mode == 3) && (delta == 0.0))))) && ((((sm0_sm + (-1.0 * _x_sm0_sm)) <= 3.0) && (-3.0 <= (sm0_sm + (-1.0 * _x_sm0_sm)))) || ( !((sm0_mode == 0) && (_x_sm0_mode == 1))))) && ((sm0_sm == _x_sm0_sm) || ( !(((sm0_mode == 1) && (_x_sm0_mode == 2)) || ((sm0_mode == 3) && (_x_sm0_mode == 0))))))) && ((((((((delta <= 0.0) || (((delta + (sm1_sm + (-1.0 * _x_sm1_sm))) == 0.0) && (sm1_mode == _x_sm1_mode))) && ((_x_sm1_mode == 1) || ( !((sm1_mode == 0) && (delta == 0.0))))) && ((_x_sm1_mode == 2) || ( !((sm1_mode == 1) && (delta == 0.0))))) && ((_x_sm1_mode == 3) || ( !((sm1_mode == 2) && (delta == 0.0))))) && ((_x_sm1_mode == 0) || ( !((sm1_mode == 3) && (delta == 0.0))))) && ((((sm1_sm + (-1.0 * _x_sm1_sm)) <= 2.0) && (-2.0 <= (sm1_sm + (-1.0 * _x_sm1_sm)))) || ( !((sm1_mode == 0) && (_x_sm1_mode == 1))))) && ((sm1_sm == _x_sm1_sm) || ( !(((sm1_mode == 1) && (_x_sm1_mode == 2)) || ((sm1_mode == 3) && (_x_sm1_mode == 0))))))) && ((((((((delta <= 0.0) || (((delta + (sm2_sm + (-1.0 * _x_sm2_sm))) == 0.0) && (sm2_mode == _x_sm2_mode))) && ((_x_sm2_mode == 1) || ( !((sm2_mode == 0) && (delta == 0.0))))) && ((_x_sm2_mode == 2) || ( !((sm2_mode == 1) && (delta == 0.0))))) && ((_x_sm2_mode == 3) || ( !((sm2_mode == 2) && (delta == 0.0))))) && ((_x_sm2_mode == 0) || ( !((sm2_mode == 3) && (delta == 0.0))))) && ((((sm2_sm + (-1.0 * _x_sm2_sm)) <= 4.0) && (-4.0 <= (sm2_sm + (-1.0 * _x_sm2_sm)))) || ( !((sm2_mode == 0) && (_x_sm2_mode == 1))))) && ((sm2_sm == _x_sm2_sm) || ( !(((sm2_mode == 1) && (_x_sm2_mode == 2)) || ((sm2_mode == 3) && (_x_sm2_mode == 0))))))) && ((((((((delta <= 0.0) || (((delta + (sm3_sm + (-1.0 * _x_sm3_sm))) == 0.0) && (sm3_mode == _x_sm3_mode))) && ((_x_sm3_mode == 1) || ( !((sm3_mode == 0) && (delta == 0.0))))) && ((_x_sm3_mode == 2) || ( !((sm3_mode == 1) && (delta == 0.0))))) && ((_x_sm3_mode == 3) || ( !((sm3_mode == 2) && (delta == 0.0))))) && ((_x_sm3_mode == 0) || ( !((sm3_mode == 3) && (delta == 0.0))))) && ((((sm3_sm + (-1.0 * _x_sm3_sm)) <= 1.0) && (-1.0 <= (sm3_sm + (-1.0 * _x_sm3_sm)))) || ( !((sm3_mode == 0) && (_x_sm3_mode == 1))))) && ((sm3_sm == _x_sm3_sm) || ( !(((sm3_mode == 1) && (_x_sm3_mode == 2)) || ((sm3_mode == 3) && (_x_sm3_mode == 0))))))) && ((((((((delta <= 0.0) || (((delta + (sm4_sm + (-1.0 * _x_sm4_sm))) == 0.0) && (sm4_mode == _x_sm4_mode))) && ((_x_sm4_mode == 1) || ( !((sm4_mode == 0) && (delta == 0.0))))) && ((_x_sm4_mode == 2) || ( !((sm4_mode == 1) && (delta == 0.0))))) && ((_x_sm4_mode == 3) || ( !((sm4_mode == 2) && (delta == 0.0))))) && ((_x_sm4_mode == 0) || ( !((sm4_mode == 3) && (delta == 0.0))))) && ((((sm4_sm + (-1.0 * _x_sm4_sm)) <= 10.0) && (-10.0 <= (sm4_sm + (-1.0 * _x_sm4_sm)))) || ( !((sm4_mode == 0) && (_x_sm4_mode == 1))))) && ((sm4_sm == _x_sm4_sm) || ( !(((sm4_mode == 1) && (_x_sm4_mode == 2)) || ((sm4_mode == 3) && (_x_sm4_mode == 0))))))) && (((delta == _x__diverge_delta) || ( !(1.0 <= _diverge_delta))) && ((1.0 <= _diverge_delta) || ((delta + (_diverge_delta + (-1.0 * _x__diverge_delta))) == 0.0))));
    sm4_sm = _x_sm4_sm;
    sm4_mode = _x_sm4_mode;
    sm3_sm = _x_sm3_sm;
    sm3_mode = _x_sm3_mode;
    delta = _x_delta;
    cm0_mode = _x_cm0_mode;
    _diverge_delta = _x__diverge_delta;
    cm0_cm = _x_cm0_cm;
    cm0_x = _x_cm0_x;
    cm1_mode = _x_cm1_mode;
    cm1_cm = _x_cm1_cm;
    cm1_x = _x_cm1_x;
    sm0_mode = _x_sm0_mode;
    sm0_sm = _x_sm0_sm;
    sm1_mode = _x_sm1_mode;
    sm1_sm = _x_sm1_sm;
    sm2_mode = _x_sm2_mode;
    sm2_sm = _x_sm2_sm;

  }
}
