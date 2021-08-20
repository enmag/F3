extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);
typedef enum {false, true} bool;
bool __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}

int main()
{
float _diverge_delta, _x__diverge_delta;
float delta, _x_delta;
float tank1_vol, _x_tank1_vol;
float tot_vol_out, _x_tot_vol_out;
float tot_vol_in, _x_tot_vol_in;
float tank0_vol, _x_tank0_vol;
bool _J513, _x__J513;
bool _J507, _x__J507;
float pipe2_flow, _x_pipe2_flow;
bool _J501, _x__J501;
bool _J495, _x__J495;
bool _EL_U_468, _x__EL_U_468;
int pipe2_mode, _x_pipe2_mode;
bool _EL_U_470, _x__EL_U_470;
bool _EL_U_472, _x__EL_U_472;
bool _EL_U_474, _x__EL_U_474;
float pipe2_dflow, _x_pipe2_dflow;
float pipe1_flow, _x_pipe1_flow;
int pipe1_mode, _x_pipe1_mode;
float pipe1_dflow, _x_pipe1_dflow;
float pipe0_flow, _x_pipe0_flow;
int pipe0_mode, _x_pipe0_mode;
float pipe0_dflow, _x_pipe0_dflow;

  int __steps_to_fair = __VERIFIER_nondet_int();
  _diverge_delta = __VERIFIER_nondet_float();
  delta = __VERIFIER_nondet_float();
  tank1_vol = __VERIFIER_nondet_float();
  tot_vol_out = __VERIFIER_nondet_float();
  tot_vol_in = __VERIFIER_nondet_float();
  tank0_vol = __VERIFIER_nondet_float();
  _J513 = __VERIFIER_nondet_bool();
  _J507 = __VERIFIER_nondet_bool();
  pipe2_flow = __VERIFIER_nondet_float();
  _J501 = __VERIFIER_nondet_bool();
  _J495 = __VERIFIER_nondet_bool();
  _EL_U_468 = __VERIFIER_nondet_bool();
  pipe2_mode = __VERIFIER_nondet_int();
  _EL_U_470 = __VERIFIER_nondet_bool();
  _EL_U_472 = __VERIFIER_nondet_bool();
  _EL_U_474 = __VERIFIER_nondet_bool();
  pipe2_dflow = __VERIFIER_nondet_float();
  pipe1_flow = __VERIFIER_nondet_float();
  pipe1_mode = __VERIFIER_nondet_int();
  pipe1_dflow = __VERIFIER_nondet_float();
  pipe0_flow = __VERIFIER_nondet_float();
  pipe0_mode = __VERIFIER_nondet_int();
  pipe0_dflow = __VERIFIER_nondet_float();

  bool __ok = (((((((((0.0 <= delta) && ((tot_vol_in == 0.0) && (tot_vol_out == 0.0))) && ((pipe0_mode == 0) && ((((((((pipe0_mode == 2) || (pipe0_mode == 1)) || ((pipe0_mode == 0) || (pipe0_mode == 3))) && ((pipe0_dflow == 0.0) || ( !((pipe0_mode == 0) || (pipe0_mode == 2))))) && (((pipe0_dflow == 1.0) || ( !(pipe0_mode == 1))) && ((pipe0_dflow == -1.0) || ( !(pipe0_mode == 3))))) && ((pipe0_flow == 0.0) || ( !(pipe0_mode == 0)))) && ((pipe0_flow == 10.0) || ( !(pipe0_mode == 2)))) && ((0.0 <= pipe0_flow) && (pipe0_flow <= 10.0))))) && ((pipe1_mode == 0) && ((((((((pipe1_mode == 2) || (pipe1_mode == 1)) || ((pipe1_mode == 0) || (pipe1_mode == 3))) && ((pipe1_dflow == 0.0) || ( !((pipe1_mode == 0) || (pipe1_mode == 2))))) && (((pipe1_dflow == 1.0) || ( !(pipe1_mode == 1))) && ((pipe1_dflow == -1.0) || ( !(pipe1_mode == 3))))) && ((pipe1_flow == 0.0) || ( !(pipe1_mode == 0)))) && ((pipe1_flow == 1.0) || ( !(pipe1_mode == 2)))) && ((0.0 <= pipe1_flow) && (pipe1_flow <= 1.0))))) && ((pipe2_mode == 0) && ((((((((pipe2_mode == 2) || (pipe2_mode == 1)) || ((pipe2_mode == 0) || (pipe2_mode == 3))) && ((pipe2_dflow == 0.0) || ( !((pipe2_mode == 0) || (pipe2_mode == 2))))) && (((pipe2_dflow == 1.0) || ( !(pipe2_mode == 1))) && ((pipe2_dflow == -1.0) || ( !(pipe2_mode == 3))))) && ((pipe2_flow == 0.0) || ( !(pipe2_mode == 0)))) && ((pipe2_flow == 1.0) || ( !(pipe2_mode == 2)))) && ((0.0 <= pipe2_flow) && (pipe2_flow <= 1.0))))) && ((tank0_vol == 0.0) && ((0.0 <= tank0_vol) && (tank0_vol <= 100.0)))) && ((tank1_vol == 0.0) && ((0.0 <= tank1_vol) && (tank1_vol <= 10.0)))) && (delta == _diverge_delta)) && ((((( !((_EL_U_474 || ( !(( !(pipe2_flow <= 0.0)) || _EL_U_472))) || (_EL_U_470 || ( !((1.0 <= _diverge_delta) || _EL_U_468))))) && ( !_J495)) && ( !_J501)) && ( !_J507)) && ( !_J513)));
  while (__steps_to_fair >= 0 && __ok) {
    if ((((_J495 && _J501) && _J507) && _J513)) {
      __steps_to_fair = __VERIFIER_nondet_int();
    } else {
      __steps_to_fair--;
    }
    _x__diverge_delta = __VERIFIER_nondet_float();
    _x_delta = __VERIFIER_nondet_float();
    _x_tank1_vol = __VERIFIER_nondet_float();
    _x_tot_vol_out = __VERIFIER_nondet_float();
    _x_tot_vol_in = __VERIFIER_nondet_float();
    _x_tank0_vol = __VERIFIER_nondet_float();
    _x__J513 = __VERIFIER_nondet_bool();
    _x__J507 = __VERIFIER_nondet_bool();
    _x_pipe2_flow = __VERIFIER_nondet_float();
    _x__J501 = __VERIFIER_nondet_bool();
    _x__J495 = __VERIFIER_nondet_bool();
    _x__EL_U_468 = __VERIFIER_nondet_bool();
    _x_pipe2_mode = __VERIFIER_nondet_int();
    _x__EL_U_470 = __VERIFIER_nondet_bool();
    _x__EL_U_472 = __VERIFIER_nondet_bool();
    _x__EL_U_474 = __VERIFIER_nondet_bool();
    _x_pipe2_dflow = __VERIFIER_nondet_float();
    _x_pipe1_flow = __VERIFIER_nondet_float();
    _x_pipe1_mode = __VERIFIER_nondet_int();
    _x_pipe1_dflow = __VERIFIER_nondet_float();
    _x_pipe0_flow = __VERIFIER_nondet_float();
    _x_pipe0_mode = __VERIFIER_nondet_int();
    _x_pipe0_dflow = __VERIFIER_nondet_float();

    __ok = (((((((((0.0 <= _x_delta) && (((tot_vol_in + ((-1.0 * _x_tot_vol_in) + ((delta * pipe0_flow) + (((1.0/2.0) * pipe0_dflow) * (delta * delta))))) == 0.0) && ((tot_vol_out + ((-1.0 * _x_tot_vol_out) + ((delta * pipe2_flow) + ((delta * delta) * ((1.0/2.0) * pipe2_dflow))))) == 0.0))) && (((((((((_x_pipe0_mode == 2) || (_x_pipe0_mode == 1)) || ((_x_pipe0_mode == 0) || (_x_pipe0_mode == 3))) && ((_x_pipe0_dflow == 0.0) || ( !((_x_pipe0_mode == 2) || (_x_pipe0_mode == 0))))) && (((_x_pipe0_dflow == 1.0) || ( !(_x_pipe0_mode == 1))) && ((_x_pipe0_dflow == -1.0) || ( !(_x_pipe0_mode == 3))))) && ((_x_pipe0_flow == 0.0) || ( !(_x_pipe0_mode == 0)))) && ((_x_pipe0_flow == 10.0) || ( !(_x_pipe0_mode == 2)))) && ((0.0 <= _x_pipe0_flow) && (_x_pipe0_flow <= 10.0))) && ((((((( !(pipe0_mode == 1)) || ((delta + (pipe0_flow + (-1.0 * _x_pipe0_flow))) == 0.0)) && (( !(pipe0_mode == 3)) || ((delta + ((-1.0 * pipe0_flow) + _x_pipe0_flow)) == 0.0))) && (((_x_pipe0_mode == 2) || (_x_pipe0_mode == 3)) || ( !((pipe0_mode == 1) && ((delta + pipe0_flow) == 10.0))))) && (((_x_pipe0_mode == 1) || (_x_pipe0_mode == 3)) || ( !((pipe0_mode == 1) && ( !((delta + pipe0_flow) <= 10.0)))))) && (((_x_pipe0_mode == 1) || (_x_pipe0_mode == 0)) || ( !((pipe0_mode == 1) && (delta == pipe0_flow))))) && (((_x_pipe0_mode == 1) || (_x_pipe0_mode == 3)) || ( !((pipe0_mode == 1) && ( !(pipe0_flow <= delta)))))))) && (((((((((_x_pipe1_mode == 2) || (_x_pipe1_mode == 1)) || ((_x_pipe1_mode == 0) || (_x_pipe1_mode == 3))) && ((_x_pipe1_dflow == 0.0) || ( !((_x_pipe1_mode == 2) || (_x_pipe1_mode == 0))))) && (((_x_pipe1_dflow == 1.0) || ( !(_x_pipe1_mode == 1))) && ((_x_pipe1_dflow == -1.0) || ( !(_x_pipe1_mode == 3))))) && ((_x_pipe1_flow == 0.0) || ( !(_x_pipe1_mode == 0)))) && ((_x_pipe1_flow == 1.0) || ( !(_x_pipe1_mode == 2)))) && ((0.0 <= _x_pipe1_flow) && (_x_pipe1_flow <= 1.0))) && ((((((( !(pipe1_mode == 1)) || ((delta + (pipe1_flow + (-1.0 * _x_pipe1_flow))) == 0.0)) && (( !(pipe1_mode == 3)) || ((delta + ((-1.0 * pipe1_flow) + _x_pipe1_flow)) == 0.0))) && (((_x_pipe1_mode == 2) || (_x_pipe1_mode == 3)) || ( !((pipe1_mode == 1) && ((delta + pipe1_flow) == 1.0))))) && (((_x_pipe1_mode == 1) || (_x_pipe1_mode == 3)) || ( !((pipe1_mode == 1) && ( !((delta + pipe1_flow) <= 1.0)))))) && (((_x_pipe1_mode == 1) || (_x_pipe1_mode == 0)) || ( !((pipe1_mode == 1) && (delta == pipe1_flow))))) && (((_x_pipe1_mode == 1) || (_x_pipe1_mode == 3)) || ( !((pipe1_mode == 1) && ( !(pipe1_flow <= delta)))))))) && (((((((((_x_pipe2_mode == 2) || (_x_pipe2_mode == 1)) || ((_x_pipe2_mode == 0) || (_x_pipe2_mode == 3))) && ((_x_pipe2_dflow == 0.0) || ( !((_x_pipe2_mode == 2) || (_x_pipe2_mode == 0))))) && (((_x_pipe2_dflow == 1.0) || ( !(_x_pipe2_mode == 1))) && ((_x_pipe2_dflow == -1.0) || ( !(_x_pipe2_mode == 3))))) && ((_x_pipe2_flow == 0.0) || ( !(_x_pipe2_mode == 0)))) && ((_x_pipe2_flow == 1.0) || ( !(_x_pipe2_mode == 2)))) && ((0.0 <= _x_pipe2_flow) && (_x_pipe2_flow <= 1.0))) && ((((((( !(pipe2_mode == 1)) || ((delta + (pipe2_flow + (-1.0 * _x_pipe2_flow))) == 0.0)) && (( !(pipe2_mode == 3)) || ((delta + ((-1.0 * pipe2_flow) + _x_pipe2_flow)) == 0.0))) && (((_x_pipe2_mode == 2) || (_x_pipe2_mode == 3)) || ( !((pipe2_mode == 1) && ((delta + pipe2_flow) == 1.0))))) && (((_x_pipe2_mode == 1) || (_x_pipe2_mode == 3)) || ( !((pipe2_mode == 1) && ( !((delta + pipe2_flow) <= 1.0)))))) && (((_x_pipe2_mode == 1) || (_x_pipe2_mode == 0)) || ( !((pipe2_mode == 1) && (delta == pipe2_flow))))) && (((_x_pipe2_mode == 1) || (_x_pipe2_mode == 3)) || ( !((pipe2_mode == 1) && ( !(pipe2_flow <= delta)))))))) && (((0.0 <= _x_tank0_vol) && (_x_tank0_vol <= 100.0)) && (((2.0 * tank0_vol) + ((-2.0 * _x_tank0_vol) + ((2.0 * (delta * (pipe0_flow + (-1.0 * pipe1_flow)))) + ((pipe0_dflow + (-1.0 * pipe1_dflow)) * (delta * delta))))) == 0.0))) && (((0.0 <= _x_tank1_vol) && (_x_tank1_vol <= 10.0)) && (((2.0 * tank1_vol) + ((-2.0 * _x_tank1_vol) + ((2.0 * (delta * (pipe1_flow + (-1.0 * pipe2_flow)))) + ((pipe1_dflow + (-1.0 * pipe2_dflow)) * (delta * delta))))) == 0.0))) && (((delta == _x__diverge_delta) || ( !(1.0 <= _diverge_delta))) && ((1.0 <= _diverge_delta) || ((delta + (_diverge_delta + (-1.0 * _x__diverge_delta))) == 0.0)))) && ((((((_EL_U_470 == (_x__EL_U_470 || ( !(_x__EL_U_468 || (1.0 <= _x__diverge_delta))))) && ((_EL_U_468 == (_x__EL_U_468 || (1.0 <= _x__diverge_delta))) && ((_EL_U_472 == (_x__EL_U_472 || ( !(_x_pipe2_flow <= 0.0)))) && (_EL_U_474 == (_x__EL_U_474 || ( !(_x__EL_U_472 || ( !(_x_pipe2_flow <= 0.0))))))))) && (_x__J495 == (( !(((_J495 && _J501) && _J507) && _J513)) && ((((_J495 && _J501) && _J507) && _J513) || ((( !(pipe2_flow <= 0.0)) || ( !(( !(pipe2_flow <= 0.0)) || _EL_U_472))) || _J495))))) && (_x__J501 == (( !(((_J495 && _J501) && _J507) && _J513)) && ((((_J495 && _J501) && _J507) && _J513) || ((( !(( !(pipe2_flow <= 0.0)) || _EL_U_472)) || ( !(_EL_U_474 || ( !(( !(pipe2_flow <= 0.0)) || _EL_U_472))))) || _J501))))) && (_x__J507 == (( !(((_J495 && _J501) && _J507) && _J513)) && ((((_J495 && _J501) && _J507) && _J513) || (((1.0 <= _diverge_delta) || ( !((1.0 <= _diverge_delta) || _EL_U_468))) || _J507))))) && (_x__J513 == (( !(((_J495 && _J501) && _J507) && _J513)) && ((((_J495 && _J501) && _J507) && _J513) || ((( !((1.0 <= _diverge_delta) || _EL_U_468)) || ( !(_EL_U_470 || ( !((1.0 <= _diverge_delta) || _EL_U_468))))) || _J513))))));
    _diverge_delta = _x__diverge_delta;
    delta = _x_delta;
    tank1_vol = _x_tank1_vol;
    tot_vol_out = _x_tot_vol_out;
    tot_vol_in = _x_tot_vol_in;
    tank0_vol = _x_tank0_vol;
    _J513 = _x__J513;
    _J507 = _x__J507;
    pipe2_flow = _x_pipe2_flow;
    _J501 = _x__J501;
    _J495 = _x__J495;
    _EL_U_468 = _x__EL_U_468;
    pipe2_mode = _x_pipe2_mode;
    _EL_U_470 = _x__EL_U_470;
    _EL_U_472 = _x__EL_U_472;
    _EL_U_474 = _x__EL_U_474;
    pipe2_dflow = _x_pipe2_dflow;
    pipe1_flow = _x_pipe1_flow;
    pipe1_mode = _x_pipe1_mode;
    pipe1_dflow = _x_pipe1_dflow;
    pipe0_flow = _x_pipe0_flow;
    pipe0_mode = _x_pipe0_mode;
    pipe0_dflow = _x_pipe0_dflow;

  }
}
