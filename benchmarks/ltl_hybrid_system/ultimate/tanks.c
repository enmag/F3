//@ ltl invariant negative: ( (<> ([] AP((pipe2_flow <= 0.0)))) || (! ([] (<> AP((1.0 <= _diverge_delta))))));
extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);
typedef enum {false, true} bool;
bool __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}

bool __ok;
float pipe1_flow, _x_pipe1_flow;
float _diverge_delta, _x__diverge_delta;
float delta, _x_delta;
int pipe1_mode, _x_pipe1_mode;
float pipe0_flow, _x_pipe0_flow;
float tank1_vol, _x_tank1_vol;
int pipe0_mode, _x_pipe0_mode;
float tot_vol_out, _x_tot_vol_out;
float tot_vol_in, _x_tot_vol_in;
float pipe2_dflow, _x_pipe2_dflow;
float pipe1_dflow, _x_pipe1_dflow;
float tank0_vol, _x_tank0_vol;
float pipe0_dflow, _x_pipe0_dflow;
float pipe2_flow, _x_pipe2_flow;
int pipe2_mode, _x_pipe2_mode;

int main()
{
  pipe1_flow = __VERIFIER_nondet_float();
  _diverge_delta = __VERIFIER_nondet_float();
  delta = __VERIFIER_nondet_float();
  pipe1_mode = __VERIFIER_nondet_int();
  pipe0_flow = __VERIFIER_nondet_float();
  tank1_vol = __VERIFIER_nondet_float();
  pipe0_mode = __VERIFIER_nondet_int();
  tot_vol_out = __VERIFIER_nondet_float();
  tot_vol_in = __VERIFIER_nondet_float();
  pipe2_dflow = __VERIFIER_nondet_float();
  pipe1_dflow = __VERIFIER_nondet_float();
  tank0_vol = __VERIFIER_nondet_float();
  pipe0_dflow = __VERIFIER_nondet_float();
  pipe2_flow = __VERIFIER_nondet_float();
  pipe2_mode = __VERIFIER_nondet_int();

  __ok = ((((((((0.0 <= delta) && ((tot_vol_in == 0.0) && (tot_vol_out == 0.0))) && ((pipe0_mode == 0) && ((((((((pipe0_mode == 2) || (pipe0_mode == 1)) || ((pipe0_mode == 0) || (pipe0_mode == 3))) && ((pipe0_dflow == 0.0) || ( !((pipe0_mode == 0) || (pipe0_mode == 2))))) && (((pipe0_dflow == 1.0) || ( !(pipe0_mode == 1))) && ((pipe0_dflow == -1.0) || ( !(pipe0_mode == 3))))) && ((pipe0_flow == 0.0) || ( !(pipe0_mode == 0)))) && ((pipe0_flow == 10.0) || ( !(pipe0_mode == 2)))) && ((0.0 <= pipe0_flow) && (pipe0_flow <= 10.0))))) && ((pipe1_mode == 0) && ((((((((pipe1_mode == 2) || (pipe1_mode == 1)) || ((pipe1_mode == 0) || (pipe1_mode == 3))) && ((pipe1_dflow == 0.0) || ( !((pipe1_mode == 0) || (pipe1_mode == 2))))) && (((pipe1_dflow == 1.0) || ( !(pipe1_mode == 1))) && ((pipe1_dflow == -1.0) || ( !(pipe1_mode == 3))))) && ((pipe1_flow == 0.0) || ( !(pipe1_mode == 0)))) && ((pipe1_flow == 1.0) || ( !(pipe1_mode == 2)))) && ((0.0 <= pipe1_flow) && (pipe1_flow <= 1.0))))) && ((pipe2_mode == 0) && ((((((((pipe2_mode == 2) || (pipe2_mode == 1)) || ((pipe2_mode == 0) || (pipe2_mode == 3))) && ((pipe2_dflow == 0.0) || ( !((pipe2_mode == 0) || (pipe2_mode == 2))))) && (((pipe2_dflow == 1.0) || ( !(pipe2_mode == 1))) && ((pipe2_dflow == -1.0) || ( !(pipe2_mode == 3))))) && ((pipe2_flow == 0.0) || ( !(pipe2_mode == 0)))) && ((pipe2_flow == 1.0) || ( !(pipe2_mode == 2)))) && ((0.0 <= pipe2_flow) && (pipe2_flow <= 1.0))))) && ((tank0_vol == 0.0) && ((0.0 <= tank0_vol) && (tank0_vol <= 100.0)))) && ((tank1_vol == 0.0) && ((0.0 <= tank1_vol) && (tank1_vol <= 10.0)))) && (delta == _diverge_delta));
  while (__ok) {
    _x_pipe1_flow = __VERIFIER_nondet_float();
    _x__diverge_delta = __VERIFIER_nondet_float();
    _x_delta = __VERIFIER_nondet_float();
    _x_pipe1_mode = __VERIFIER_nondet_int();
    _x_pipe0_flow = __VERIFIER_nondet_float();
    _x_tank1_vol = __VERIFIER_nondet_float();
    _x_pipe0_mode = __VERIFIER_nondet_int();
    _x_tot_vol_out = __VERIFIER_nondet_float();
    _x_tot_vol_in = __VERIFIER_nondet_float();
    _x_pipe2_dflow = __VERIFIER_nondet_float();
    _x_pipe1_dflow = __VERIFIER_nondet_float();
    _x_tank0_vol = __VERIFIER_nondet_float();
    _x_pipe0_dflow = __VERIFIER_nondet_float();
    _x_pipe2_flow = __VERIFIER_nondet_float();
    _x_pipe2_mode = __VERIFIER_nondet_int();

    __ok = ((((((((0.0 <= _x_delta) && (((tot_vol_in + ((-1.0 * _x_tot_vol_in) + ((delta * pipe0_flow) + (((1.0/2.0) * pipe0_dflow) * (delta * delta))))) == 0.0) && ((tot_vol_out + ((-1.0 * _x_tot_vol_out) + ((delta * pipe2_flow) + ((delta * delta) * ((1.0/2.0) * pipe2_dflow))))) == 0.0))) && (((((((((_x_pipe0_mode == 2) || (_x_pipe0_mode == 1)) || ((_x_pipe0_mode == 0) || (_x_pipe0_mode == 3))) && ((_x_pipe0_dflow == 0.0) || ( !((_x_pipe0_mode == 2) || (_x_pipe0_mode == 0))))) && (((_x_pipe0_dflow == 1.0) || ( !(_x_pipe0_mode == 1))) && ((_x_pipe0_dflow == -1.0) || ( !(_x_pipe0_mode == 3))))) && ((_x_pipe0_flow == 0.0) || ( !(_x_pipe0_mode == 0)))) && ((_x_pipe0_flow == 10.0) || ( !(_x_pipe0_mode == 2)))) && ((0.0 <= _x_pipe0_flow) && (_x_pipe0_flow <= 10.0))) && ((((((( !(pipe0_mode == 1)) || ((delta + (pipe0_flow + (-1.0 * _x_pipe0_flow))) == 0.0)) && (( !(pipe0_mode == 3)) || ((delta + ((-1.0 * pipe0_flow) + _x_pipe0_flow)) == 0.0))) && (((_x_pipe0_mode == 2) || (_x_pipe0_mode == 3)) || ( !((pipe0_mode == 1) && ((delta + pipe0_flow) == 10.0))))) && (((_x_pipe0_mode == 1) || (_x_pipe0_mode == 3)) || ( !((pipe0_mode == 1) && ( !((delta + pipe0_flow) <= 10.0)))))) && (((_x_pipe0_mode == 1) || (_x_pipe0_mode == 0)) || ( !((pipe0_mode == 1) && (delta == pipe0_flow))))) && (((_x_pipe0_mode == 1) || (_x_pipe0_mode == 3)) || ( !((pipe0_mode == 1) && ( !(pipe0_flow <= delta)))))))) && (((((((((_x_pipe1_mode == 2) || (_x_pipe1_mode == 1)) || ((_x_pipe1_mode == 0) || (_x_pipe1_mode == 3))) && ((_x_pipe1_dflow == 0.0) || ( !((_x_pipe1_mode == 2) || (_x_pipe1_mode == 0))))) && (((_x_pipe1_dflow == 1.0) || ( !(_x_pipe1_mode == 1))) && ((_x_pipe1_dflow == -1.0) || ( !(_x_pipe1_mode == 3))))) && ((_x_pipe1_flow == 0.0) || ( !(_x_pipe1_mode == 0)))) && ((_x_pipe1_flow == 1.0) || ( !(_x_pipe1_mode == 2)))) && ((0.0 <= _x_pipe1_flow) && (_x_pipe1_flow <= 1.0))) && ((((((( !(pipe1_mode == 1)) || ((delta + (pipe1_flow + (-1.0 * _x_pipe1_flow))) == 0.0)) && (( !(pipe1_mode == 3)) || ((delta + ((-1.0 * pipe1_flow) + _x_pipe1_flow)) == 0.0))) && (((_x_pipe1_mode == 2) || (_x_pipe1_mode == 3)) || ( !((pipe1_mode == 1) && ((delta + pipe1_flow) == 1.0))))) && (((_x_pipe1_mode == 1) || (_x_pipe1_mode == 3)) || ( !((pipe1_mode == 1) && ( !((delta + pipe1_flow) <= 1.0)))))) && (((_x_pipe1_mode == 1) || (_x_pipe1_mode == 0)) || ( !((pipe1_mode == 1) && (delta == pipe1_flow))))) && (((_x_pipe1_mode == 1) || (_x_pipe1_mode == 3)) || ( !((pipe1_mode == 1) && ( !(pipe1_flow <= delta)))))))) && (((((((((_x_pipe2_mode == 2) || (_x_pipe2_mode == 1)) || ((_x_pipe2_mode == 0) || (_x_pipe2_mode == 3))) && ((_x_pipe2_dflow == 0.0) || ( !((_x_pipe2_mode == 2) || (_x_pipe2_mode == 0))))) && (((_x_pipe2_dflow == 1.0) || ( !(_x_pipe2_mode == 1))) && ((_x_pipe2_dflow == -1.0) || ( !(_x_pipe2_mode == 3))))) && ((_x_pipe2_flow == 0.0) || ( !(_x_pipe2_mode == 0)))) && ((_x_pipe2_flow == 1.0) || ( !(_x_pipe2_mode == 2)))) && ((0.0 <= _x_pipe2_flow) && (_x_pipe2_flow <= 1.0))) && ((((((( !(pipe2_mode == 1)) || ((delta + (pipe2_flow + (-1.0 * _x_pipe2_flow))) == 0.0)) && (( !(pipe2_mode == 3)) || ((delta + ((-1.0 * pipe2_flow) + _x_pipe2_flow)) == 0.0))) && (((_x_pipe2_mode == 2) || (_x_pipe2_mode == 3)) || ( !((pipe2_mode == 1) && ((delta + pipe2_flow) == 1.0))))) && (((_x_pipe2_mode == 1) || (_x_pipe2_mode == 3)) || ( !((pipe2_mode == 1) && ( !((delta + pipe2_flow) <= 1.0)))))) && (((_x_pipe2_mode == 1) || (_x_pipe2_mode == 0)) || ( !((pipe2_mode == 1) && (delta == pipe2_flow))))) && (((_x_pipe2_mode == 1) || (_x_pipe2_mode == 3)) || ( !((pipe2_mode == 1) && ( !(pipe2_flow <= delta)))))))) && (((0.0 <= _x_tank0_vol) && (_x_tank0_vol <= 100.0)) && (((2.0 * tank0_vol) + ((-2.0 * _x_tank0_vol) + ((2.0 * (delta * (pipe0_flow + (-1.0 * pipe1_flow)))) + ((pipe0_dflow + (-1.0 * pipe1_dflow)) * (delta * delta))))) == 0.0))) && (((0.0 <= _x_tank1_vol) && (_x_tank1_vol <= 10.0)) && (((2.0 * tank1_vol) + ((-2.0 * _x_tank1_vol) + ((2.0 * (delta * (pipe1_flow + (-1.0 * pipe2_flow)))) + ((pipe1_dflow + (-1.0 * pipe2_dflow)) * (delta * delta))))) == 0.0))) && (((delta == _x__diverge_delta) || ( !(1.0 <= _diverge_delta))) && ((1.0 <= _diverge_delta) || ((delta + (_diverge_delta + (-1.0 * _x__diverge_delta))) == 0.0))));
    pipe1_flow = _x_pipe1_flow;
    _diverge_delta = _x__diverge_delta;
    delta = _x_delta;
    pipe1_mode = _x_pipe1_mode;
    pipe0_flow = _x_pipe0_flow;
    tank1_vol = _x_tank1_vol;
    pipe0_mode = _x_pipe0_mode;
    tot_vol_out = _x_tot_vol_out;
    tot_vol_in = _x_tot_vol_in;
    pipe2_dflow = _x_pipe2_dflow;
    pipe1_dflow = _x_pipe1_dflow;
    tank0_vol = _x_tank0_vol;
    pipe0_dflow = _x_pipe0_dflow;
    pipe2_flow = _x_pipe2_flow;
    pipe2_mode = _x_pipe2_mode;

  }
}
