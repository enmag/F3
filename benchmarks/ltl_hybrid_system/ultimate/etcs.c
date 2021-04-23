//@ ltl invariant negative: ( (<> ([] (! ( (! AP((delta <= 0.0))) && (! AP((train_v <= 0.0))))))) || (! ([] (<> AP((1.0 <= _diverge_delta))))));

extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);

char __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}


float train_a, _x_train_a;
float train_v, _x_train_v;
float train_z, _x_train_z;
float train_c, _x_train_c;
float rbc_v_des, _x_rbc_v_des;
float rbc_d, _x_rbc_d;
float rbc_m, _x_rbc_m;
char rbc_s, _x_rbc_s;
float _diverge_delta, _x__diverge_delta;
float delta, _x_delta;

int main()
{
  train_a = __VERIFIER_nondet_float();
  train_v = __VERIFIER_nondet_float();
  train_z = __VERIFIER_nondet_float();
  train_c = __VERIFIER_nondet_float();
  rbc_v_des = __VERIFIER_nondet_float();
  rbc_d = __VERIFIER_nondet_float();
  rbc_m = __VERIFIER_nondet_float();
  rbc_s = __VERIFIER_nondet_bool();
  _diverge_delta = __VERIFIER_nondet_float();
  delta = __VERIFIER_nondet_float();

  int __ok = (((((((rbc_s != 0) && (rbc_v_des == 0.0)) && ((( !(rbc_m <= train_z)) && (train_v == 0.0)) && ((train_a == 0.0) && (train_c == 0.0)))) && (((0.0 <= delta) && (0.0 <= rbc_m)) && ((0.0 <= rbc_d) && (0.0 <= rbc_v_des)))) && (((train_c <= 1.0) && (0.0 <= train_z)) && ((-2.0 <= train_a) && (train_a <= 4.0)))) && ((train_a <= 0.0) || ( !(rbc_v_des <= train_v)))) && (delta == _diverge_delta));
  while (__ok) {
    _x_train_a = __VERIFIER_nondet_float();
    _x_train_v = __VERIFIER_nondet_float();
    _x_train_z = __VERIFIER_nondet_float();
    _x_train_c = __VERIFIER_nondet_float();
    _x_rbc_v_des = __VERIFIER_nondet_float();
    _x_rbc_d = __VERIFIER_nondet_float();
    _x_rbc_m = __VERIFIER_nondet_float();
    _x_rbc_s = __VERIFIER_nondet_bool();
    _x__diverge_delta = __VERIFIER_nondet_float();
    _x_delta = __VERIFIER_nondet_float();

    __ok = (((((((((((((0.0 <= _x_delta) && (0.0 <= _x_rbc_m)) && ((0.0 <= _x_rbc_d) && (0.0 <= _x_rbc_v_des))) && (((_x_train_c <= 1.0) && (0.0 <= _x_train_z)) && ((-2.0 <= _x_train_a) && (_x_train_a <= 4.0)))) && ((_x_train_a <= 0.0) || ( !(_x_rbc_v_des <= _x_train_v)))) && (( !(_x_rbc_s != 0)) || ((rbc_m == _x_rbc_m) && (rbc_d == _x_rbc_d)))) && ((_x_rbc_s != 0) || (((4.0 * rbc_m) + ((-4.0 * _x_rbc_m) + ((rbc_d * rbc_d) + (-1.0 * (_x_rbc_d * _x_rbc_d))))) <= 0.0))) && ((1.0 <= train_c) || ((delta + (train_c + (-1.0 * _x_train_c))) == 0.0))) && (( !(1.0 <= train_c)) || ((train_c == 0.0) && (delta == 0.0)))) && (((2.0 * train_z) + ((-2.0 * _x_train_z) + ((train_a * (delta * delta)) + (2.0 * (delta * train_v))))) == 0.0)) && ((train_v + ((-1.0 * _x_train_v) + (delta * train_a))) == 0.0)) && ((_x_train_a == -2.0) || ( !(((train_c == 1.0) && (_x_train_c == 0.0)) && ((rbc_s != 0) || (((4.0 * rbc_m) + ((-4.0 * train_z) + ((-4.0 * train_v) + ((-1.0 * (train_v * train_v)) + (rbc_d * rbc_d))))) <= 24.0)))))) && (((delta == _x__diverge_delta) || ( !(1.0 <= _diverge_delta))) && ((1.0 <= _diverge_delta) || ((delta + (_diverge_delta + (-1.0 * _x__diverge_delta))) == 0.0))));
    train_a = _x_train_a;
    train_v = _x_train_v;
    train_z = _x_train_z;
    train_c = _x_train_c;
    rbc_v_des = _x_rbc_v_des;
    rbc_d = _x_rbc_d;
    rbc_m = _x_rbc_m;
    rbc_s = _x_rbc_s;
    _diverge_delta = _x__diverge_delta;
    delta = _x_delta;

  }
}
