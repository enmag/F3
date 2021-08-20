//@ ltl invariant negative: ( (<> ([] (! ( (! AP((delta <= 0.0))) && (! AP((train_v <= 0.0))))))) || (! ([] (<> AP((1.0 <= _diverge_delta))))));
extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);
typedef enum {false, true} bool;
bool __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}

bool __ok;
float rbc_d, _x_rbc_d;
float _diverge_delta, _x__diverge_delta;
float rbc_m, _x_rbc_m;
float delta, _x_delta;
float train_v, _x_train_v;
float rbc_v_des, _x_rbc_v_des;
float train_a, _x_train_a;
bool rbc_s, _x_rbc_s;
float train_z, _x_train_z;
float train_c, _x_train_c;

int main()
{
  rbc_d = __VERIFIER_nondet_float();
  _diverge_delta = __VERIFIER_nondet_float();
  rbc_m = __VERIFIER_nondet_float();
  delta = __VERIFIER_nondet_float();
  train_v = __VERIFIER_nondet_float();
  rbc_v_des = __VERIFIER_nondet_float();
  train_a = __VERIFIER_nondet_float();
  rbc_s = __VERIFIER_nondet_bool();
  train_z = __VERIFIER_nondet_float();
  train_c = __VERIFIER_nondet_float();

  __ok = (((((((rbc_s && (rbc_v_des == 0.0)) && ((( !(rbc_m <= train_z)) && (train_v == 0.0)) && ((train_a == 0.0) && (train_c == 0.0)))) && (((0.0 <= delta) && (0.0 <= rbc_m)) && ((0.0 <= rbc_d) && (0.0 <= rbc_v_des)))) && (((train_c <= 1.0) && (0.0 <= train_z)) && ((-2.0 <= train_a) && (train_a <= 4.0)))) && ((train_a <= 0.0) || ( !(rbc_v_des <= train_v)))) && (0.0 <= train_v)) && (delta == _diverge_delta));
  while (__ok) {
    _x_rbc_d = __VERIFIER_nondet_float();
    _x__diverge_delta = __VERIFIER_nondet_float();
    _x_rbc_m = __VERIFIER_nondet_float();
    _x_delta = __VERIFIER_nondet_float();
    _x_train_v = __VERIFIER_nondet_float();
    _x_rbc_v_des = __VERIFIER_nondet_float();
    _x_train_a = __VERIFIER_nondet_float();
    _x_rbc_s = __VERIFIER_nondet_bool();
    _x_train_z = __VERIFIER_nondet_float();
    _x_train_c = __VERIFIER_nondet_float();

    __ok = ((((((((((((((0.0 <= _x_delta) && (0.0 <= _x_rbc_m)) && ((0.0 <= _x_rbc_d) && (0.0 <= _x_rbc_v_des))) && (((_x_train_c <= 1.0) && (0.0 <= _x_train_z)) && ((-2.0 <= _x_train_a) && (_x_train_a <= 4.0)))) && ((_x_train_a <= 0.0) || ( !(_x_rbc_v_des <= _x_train_v)))) && (0.0 <= _x_train_v)) && (( !_x_rbc_s) || ((rbc_m == _x_rbc_m) && (rbc_d == _x_rbc_d)))) && (_x_rbc_s || (((4.0 * rbc_m) + ((-4.0 * _x_rbc_m) + ((rbc_d * rbc_d) + (-1.0 * (_x_rbc_d * _x_rbc_d))))) <= 0.0))) && ((1.0 <= train_c) || ((delta + (train_c + (-1.0 * _x_train_c))) == 0.0))) && (( !(1.0 <= train_c)) || ((_x_train_c == 0.0) && (delta == 0.0)))) && (((2.0 * train_z) + ((-2.0 * _x_train_z) + ((train_a * (delta * delta)) + (2.0 * (delta * train_v))))) == 0.0)) && ((train_v + ((-1.0 * _x_train_v) + (delta * train_a))) == 0.0)) && ((_x_train_a == -2.0) || ( !(((_x_train_c == 0.0) && (train_c == 1.0)) && (rbc_s || (((4.0 * rbc_m) + ((-4.0 * train_z) + ((-4.0 * train_v) + ((-1.0 * (train_v * train_v)) + (rbc_d * rbc_d))))) <= 24.0)))))) && (((delta == _x__diverge_delta) || ( !(1.0 <= _diverge_delta))) && ((1.0 <= _diverge_delta) || ((delta + (_diverge_delta + (-1.0 * _x__diverge_delta))) == 0.0))));
    rbc_d = _x_rbc_d;
    _diverge_delta = _x__diverge_delta;
    rbc_m = _x_rbc_m;
    delta = _x_delta;
    train_v = _x_train_v;
    rbc_v_des = _x_rbc_v_des;
    train_a = _x_train_a;
    rbc_s = _x_rbc_s;
    train_z = _x_train_z;
    train_c = _x_train_c;

  }
}
