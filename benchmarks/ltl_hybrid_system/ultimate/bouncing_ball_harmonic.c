//@ ltl invariant negative: ( (<> ([] (! ( AP((h == 0.0)) && (! AP((v <= 0.0))))))) || (! ([] (<> AP((1.0 <= _diverge_delta))))));
extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);
typedef enum {false, true} bool;
bool __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}

bool __ok;
float _diverge_delta, _x__diverge_delta;
float delta, _x_delta;
float v, _x_v;
float h, _x_h;
int counter, _x_counter;
bool stop, _x_stop;

int main()
{
  _diverge_delta = __VERIFIER_nondet_float();
  delta = __VERIFIER_nondet_float();
  v = __VERIFIER_nondet_float();
  h = __VERIFIER_nondet_float();
  counter = __VERIFIER_nondet_int();
  stop = __VERIFIER_nondet_bool();

  __ok = ((((counter == 1) && (h == 0.0)) && ((v == (981.0/200.0)) && (0.0 <= delta))) && (delta == _diverge_delta));
  while (__ok) {
    _x__diverge_delta = __VERIFIER_nondet_float();
    _x_delta = __VERIFIER_nondet_float();
    _x_v = __VERIFIER_nondet_float();
    _x_h = __VERIFIER_nondet_float();
    _x_counter = __VERIFIER_nondet_int();
    _x_stop = __VERIFIER_nondet_bool();

    __ok = ((((((((counter + (-1 * _x_counter)) == -1) || ( !((h == 0.0) && ( !(0.0 <= v))))) && (((h == 0.0) && ( !(0.0 <= v))) || (counter == _x_counter))) && (((_x_h == 0.0) || ( !((h == 0.0) && (stop || (v <= 0.0))))) && (((h == 0.0) && (stop || (v <= 0.0))) || (((200.0 * h) + ((-200.0 * _x_h) + ((200.0 * (v * delta)) + (-981.0 * (delta * delta))))) == 0.0)))) && (((_x_v == 0.0) || ( !(stop && (h == 0.0)))) && ((((_x_v + ((v * ((float)(counter))) / ((float)((counter + 1))))) == 0.0) || ( !(( !stop) && ((h == 0.0) && (v <= 0.0))))) && (((stop && (h == 0.0)) || (( !stop) && ((h == 0.0) && (v <= 0.0)))) || (((100.0 * v) + ((-100.0 * _x_v) + (-981.0 * delta))) == 0.0))))) && (((0.0 <= _x_h) && (0.0 <= _x_delta)) && ((_x_delta == 0.0) || ( !((_x_h == 0.0) && ( !(0.0 <= _x_v))))))) && (((delta == _x__diverge_delta) || ( !(1.0 <= _diverge_delta))) && ((1.0 <= _diverge_delta) || ((delta + (_diverge_delta + (-1.0 * _x__diverge_delta))) == 0.0))));
    _diverge_delta = _x__diverge_delta;
    delta = _x_delta;
    v = _x_v;
    h = _x_h;
    counter = _x_counter;
    stop = _x_stop;

  }
}
