//@ ltl invariant negative: ( (<> ([] AP((pipe2_flow <= 0.0)))) || (! ([] (<> AP((1.0 <= _diverge_delta))))));

extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);

char __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}


float delta, _x_delta;
int pipe0_mode, _x_pipe0_mode;
float pipe0_flow, _x_pipe0_flow;
float pipe0_dflow, _x_pipe0_dflow;
int pipe1_mode, _x_pipe1_mode;
float pipe1_flow, _x_pipe1_flow;
float pipe1_dflow, _x_pipe1_dflow;
int pipe2_mode, _x_pipe2_mode;
float pipe2_flow, _x_pipe2_flow;
float pipe2_dflow, _x_pipe2_dflow;
float tank0_vol, _x_tank0_vol;
float tank1_vol, _x_tank1_vol;
float _diverge_delta, _x__diverge_delta;

int main()
{
  delta = __VERIFIER_nondet_float();
  pipe0_mode = __VERIFIER_nondet_int();
  pipe0_flow = __VERIFIER_nondet_float();
  pipe0_dflow = __VERIFIER_nondet_float();
  pipe1_mode = __VERIFIER_nondet_int();
  pipe1_flow = __VERIFIER_nondet_float();
  pipe1_dflow = __VERIFIER_nondet_float();
  pipe2_mode = __VERIFIER_nondet_int();
  pipe2_flow = __VERIFIER_nondet_float();
  pipe2_dflow = __VERIFIER_nondet_float();
  tank0_vol = __VERIFIER_nondet_float();
  tank1_vol = __VERIFIER_nondet_float();
  _diverge_delta = __VERIFIER_nondet_float();

  int __ok = (((((((0.0 <= delta) && ((pipe0_mode == 0) && (((((((pipe0_dflow == 0.0) || ( !((pipe0_mode == 0) || (pipe0_mode == 2)))) && ((pipe0_dflow == 1.0) || ( !(((pipe0_mode == 0) || (pipe0_mode == 2)) && (pipe0_mode == 1))))) && ((pipe0_dflow == -1.0) || ( !(((pipe0_mode == 0) || (pipe0_mode == 2)) && ( !(pipe0_mode == 1)))))) && ((pipe0_flow == 0.0) || ( !(pipe0_mode == 0)))) && ((pipe0_flow == 10.0) || ( !(pipe0_mode == 2)))) && ((0.0 <= pipe0_flow) && (pipe0_flow <= 10.0))))) && ((pipe1_mode == 0) && (((((((pipe1_dflow == 0.0) || ( !((pipe1_mode == 0) || (pipe1_mode == 2)))) && ((pipe1_dflow == 1.0) || ( !(((pipe1_mode == 0) || (pipe1_mode == 2)) && (pipe1_mode == 1))))) && ((pipe1_dflow == -1.0) || ( !(((pipe1_mode == 0) || (pipe1_mode == 2)) && ( !(pipe1_mode == 1)))))) && ((pipe1_flow == 0.0) || ( !(pipe1_mode == 0)))) && ((pipe1_flow == 1.0) || ( !(pipe1_mode == 2)))) && ((0.0 <= pipe1_flow) && (pipe1_flow <= 1.0))))) && ((pipe2_mode == 0) && (((((((pipe2_dflow == 0.0) || ( !((pipe2_mode == 0) || (pipe2_mode == 2)))) && ((pipe2_dflow == 1.0) || ( !(((pipe2_mode == 0) || (pipe2_mode == 2)) && (pipe2_mode == 1))))) && ((pipe2_dflow == -1.0) || ( !(((pipe2_mode == 0) || (pipe2_mode == 2)) && ( !(pipe2_mode == 1)))))) && ((pipe2_flow == 0.0) || ( !(pipe2_mode == 0)))) && ((pipe2_flow == 1.0) || ( !(pipe2_mode == 2)))) && ((0.0 <= pipe2_flow) && (pipe2_flow <= 1.0))))) && ((tank0_vol == 0.0) && ((0.0 <= tank0_vol) && (tank0_vol <= 100.0)))) && ((tank1_vol == 0.0) && ((0.0 <= tank1_vol) && (tank1_vol <= 10.0)))) && (delta == _diverge_delta));
  while (__ok) {
    _x_delta = __VERIFIER_nondet_float();
    _x_pipe0_mode = __VERIFIER_nondet_int();
    _x_pipe0_flow = __VERIFIER_nondet_float();
    _x_pipe0_dflow = __VERIFIER_nondet_float();
    _x_pipe1_mode = __VERIFIER_nondet_int();
    _x_pipe1_flow = __VERIFIER_nondet_float();
    _x_pipe1_dflow = __VERIFIER_nondet_float();
    _x_pipe2_mode = __VERIFIER_nondet_int();
    _x_pipe2_flow = __VERIFIER_nondet_float();
    _x_pipe2_dflow = __VERIFIER_nondet_float();
    _x_tank0_vol = __VERIFIER_nondet_float();
    _x_tank1_vol = __VERIFIER_nondet_float();
    _x__diverge_delta = __VERIFIER_nondet_float();

    __ok = (((((((0.0 <= _x_delta) && ((((((((_x_pipe0_dflow == 0.0) || ( !((_x_pipe0_mode == 0) || (_x_pipe0_mode == 2)))) && ((_x_pipe0_dflow == 1.0) || ( !(((_x_pipe0_mode == 0) || (_x_pipe0_mode == 2)) && (_x_pipe0_mode == 1))))) && ((_x_pipe0_dflow == -1.0) || ( !(((_x_pipe0_mode == 0) || (_x_pipe0_mode == 2)) && ( !(_x_pipe0_mode == 1)))))) && ((_x_pipe0_flow == 0.0) || ( !(_x_pipe0_mode == 0)))) && ((_x_pipe0_flow == 10.0) || ( !(_x_pipe0_mode == 2)))) && ((0.0 <= _x_pipe0_flow) && (_x_pipe0_flow <= 10.0))) && ((((((( !(pipe0_mode == 1)) || ((delta + (pipe0_flow + (-1.0 * _x_pipe0_flow))) == 0.0)) && (((delta + ((-1.0 * pipe0_flow) + _x_pipe0_flow)) == 0.0) || ( !(pipe0_mode == 3)))) && (((_x_pipe0_mode == 2) || (_x_pipe0_mode == 3)) || ( !((pipe0_mode == 1) && ((delta + pipe0_flow) == 10.0))))) && (((_x_pipe0_mode == 1) || (_x_pipe0_mode == 3)) || ( !((pipe0_mode == 1) && ( !((delta + pipe0_flow) <= 10.0)))))) && (((_x_pipe0_mode == 0) || (_x_pipe0_mode == 1)) || ( !((pipe0_mode == 1) && (delta == pipe0_flow))))) && (((_x_pipe0_mode == 1) || (_x_pipe0_mode == 3)) || ( !((pipe0_mode == 1) && ( !(pipe0_flow <= delta)))))))) && ((((((((_x_pipe1_dflow == 0.0) || ( !((_x_pipe1_mode == 0) || (_x_pipe1_mode == 2)))) && ((_x_pipe1_dflow == 1.0) || ( !(((_x_pipe1_mode == 0) || (_x_pipe1_mode == 2)) && (_x_pipe1_mode == 1))))) && ((_x_pipe1_dflow == -1.0) || ( !(((_x_pipe1_mode == 0) || (_x_pipe1_mode == 2)) && ( !(_x_pipe1_mode == 1)))))) && ((_x_pipe1_flow == 0.0) || ( !(_x_pipe1_mode == 0)))) && ((_x_pipe1_flow == 1.0) || ( !(_x_pipe1_mode == 2)))) && ((0.0 <= _x_pipe1_flow) && (_x_pipe1_flow <= 1.0))) && ((((((( !(pipe1_mode == 1)) || ((delta + (pipe1_flow + (-1.0 * _x_pipe1_flow))) == 0.0)) && (((delta + ((-1.0 * pipe1_flow) + _x_pipe1_flow)) == 0.0) || ( !(pipe1_mode == 3)))) && (((_x_pipe1_mode == 2) || (_x_pipe1_mode == 3)) || ( !((pipe1_mode == 1) && ((delta + pipe1_flow) == 1.0))))) && (((_x_pipe1_mode == 1) || (_x_pipe1_mode == 3)) || ( !((pipe1_mode == 1) && ( !((delta + pipe1_flow) <= 1.0)))))) && (((_x_pipe1_mode == 0) || (_x_pipe1_mode == 1)) || ( !((pipe1_mode == 1) && (delta == pipe1_flow))))) && (((_x_pipe1_mode == 1) || (_x_pipe1_mode == 3)) || ( !((pipe1_mode == 1) && ( !(pipe1_flow <= delta)))))))) && ((((((((_x_pipe2_dflow == 0.0) || ( !((_x_pipe2_mode == 0) || (_x_pipe2_mode == 2)))) && ((_x_pipe2_dflow == 1.0) || ( !(((_x_pipe2_mode == 0) || (_x_pipe2_mode == 2)) && (_x_pipe2_mode == 1))))) && ((_x_pipe2_dflow == -1.0) || ( !(((_x_pipe2_mode == 0) || (_x_pipe2_mode == 2)) && ( !(_x_pipe2_mode == 1)))))) && ((_x_pipe2_flow == 0.0) || ( !(_x_pipe2_mode == 0)))) && ((_x_pipe2_flow == 1.0) || ( !(_x_pipe2_mode == 2)))) && ((0.0 <= _x_pipe2_flow) && (_x_pipe2_flow <= 1.0))) && ((((((( !(pipe2_mode == 1)) || ((delta + (pipe2_flow + (-1.0 * _x_pipe2_flow))) == 0.0)) && (((delta + ((-1.0 * pipe2_flow) + _x_pipe2_flow)) == 0.0) || ( !(pipe2_mode == 3)))) && (((_x_pipe2_mode == 2) || (_x_pipe2_mode == 3)) || ( !((pipe2_mode == 1) && ((delta + pipe2_flow) == 1.0))))) && (((_x_pipe2_mode == 1) || (_x_pipe2_mode == 3)) || ( !((pipe2_mode == 1) && ( !((delta + pipe2_flow) <= 1.0)))))) && (((_x_pipe2_mode == 0) || (_x_pipe2_mode == 1)) || ( !((pipe2_mode == 1) && (delta == pipe2_flow))))) && (((_x_pipe2_mode == 1) || (_x_pipe2_mode == 3)) || ( !((pipe2_mode == 1) && ( !(pipe2_flow <= delta)))))))) && (((0.0 <= _x_tank0_vol) && (_x_tank0_vol <= 100.0)) && (((2.0 * tank0_vol) + ((-2.0 * _x_tank0_vol) + ((2.0 * (delta * (pipe0_flow + (-1.0 * pipe1_flow)))) + ((pipe0_dflow + (-1.0 * pipe1_dflow)) * (delta * delta))))) == 0.0))) && (((0.0 <= _x_tank1_vol) && (_x_tank1_vol <= 10.0)) && (((2.0 * tank1_vol) + ((-2.0 * _x_tank1_vol) + ((2.0 * (delta * (pipe1_flow + (-1.0 * pipe2_flow)))) + ((pipe1_dflow + (-1.0 * pipe2_dflow)) * (delta * delta))))) == 0.0))) && (((delta == _x__diverge_delta) || ( !(1.0 <= _diverge_delta))) && ((1.0 <= _diverge_delta) || ((delta + (_diverge_delta + (-1.0 * _x__diverge_delta))) == 0.0))));
    delta = _x_delta;
    pipe0_mode = _x_pipe0_mode;
    pipe0_flow = _x_pipe0_flow;
    pipe0_dflow = _x_pipe0_dflow;
    pipe1_mode = _x_pipe1_mode;
    pipe1_flow = _x_pipe1_flow;
    pipe1_dflow = _x_pipe1_dflow;
    pipe2_mode = _x_pipe2_mode;
    pipe2_flow = _x_pipe2_flow;
    pipe2_dflow = _x_pipe2_dflow;
    tank0_vol = _x_tank0_vol;
    tank1_vol = _x_tank1_vol;
    _diverge_delta = _x__diverge_delta;

  }
}
