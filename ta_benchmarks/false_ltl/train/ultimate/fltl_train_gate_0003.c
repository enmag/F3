//@ ltl invariant negative: ( ([] ( (<> ( ( AP((gate_l1 != 0)) && (! AP((gate_l0 != 0)))) && ( (X AP((gate_l1 != 0))) && (X AP((gate_l0 != 0)))))) || (! ( ( (! AP((gate_l0 != 0))) && (! AP((gate_l1 != 0)))) && ( (! (X AP((gate_l1 != 0)))) && (X AP((gate_l0 != 0)))))))) || (! ([] (<> AP((1.0 <= _diverge_delta))))));

extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);

char __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}


float _diverge_delta, _x__diverge_delta;
char t2_l1, _x_t2_l1;
char t2_l0, _x_t2_l0;
char t2_evt1, _x_t2_evt1;
char t2_evt0, _x_t2_evt0;
char t1_l1, _x_t1_l1;
char t1_l0, _x_t1_l0;
char t1_evt1, _x_t1_evt1;
char t1_evt0, _x_t1_evt0;
float t1_x, _x_t1_x;
char t0_l1, _x_t0_l1;
char t0_evt1, _x_t0_evt1;
char t0_evt0, _x_t0_evt0;
float t0_x, _x_t0_x;
float delta, _x_delta;
float t2_x, _x_t2_x;
char gate_l0, _x_gate_l0;
char controller_l0, _x_controller_l0;
char gate_l1, _x_gate_l1;
float gate_y, _x_gate_y;
char controller_l1, _x_controller_l1;
char gate_evt0, _x_gate_evt0;
char controller_evt0, _x_controller_evt0;
char controller_evt1, _x_controller_evt1;
char gate_evt1, _x_gate_evt1;
float controller_z, _x_controller_z;
char t0_l0, _x_t0_l0;
char controller_evt2, _x_controller_evt2;
int controller_cnt, _x_controller_cnt;

int main()
{
  _diverge_delta = __VERIFIER_nondet_float();
  t2_l1 = __VERIFIER_nondet_bool();
  t2_l0 = __VERIFIER_nondet_bool();
  t2_evt1 = __VERIFIER_nondet_bool();
  t2_evt0 = __VERIFIER_nondet_bool();
  t1_l1 = __VERIFIER_nondet_bool();
  t1_l0 = __VERIFIER_nondet_bool();
  t1_evt1 = __VERIFIER_nondet_bool();
  t1_evt0 = __VERIFIER_nondet_bool();
  t1_x = __VERIFIER_nondet_float();
  t0_l1 = __VERIFIER_nondet_bool();
  t0_evt1 = __VERIFIER_nondet_bool();
  t0_evt0 = __VERIFIER_nondet_bool();
  t0_x = __VERIFIER_nondet_float();
  delta = __VERIFIER_nondet_float();
  t2_x = __VERIFIER_nondet_float();
  gate_l0 = __VERIFIER_nondet_bool();
  controller_l0 = __VERIFIER_nondet_bool();
  gate_l1 = __VERIFIER_nondet_bool();
  gate_y = __VERIFIER_nondet_float();
  controller_l1 = __VERIFIER_nondet_bool();
  gate_evt0 = __VERIFIER_nondet_bool();
  controller_evt0 = __VERIFIER_nondet_bool();
  controller_evt1 = __VERIFIER_nondet_bool();
  gate_evt1 = __VERIFIER_nondet_bool();
  controller_z = __VERIFIER_nondet_float();
  t0_l0 = __VERIFIER_nondet_bool();
  controller_evt2 = __VERIFIER_nondet_bool();
  controller_cnt = __VERIFIER_nondet_int();

  int __ok = (((((((( !(t2_l0 != 0)) && ( !(t2_l1 != 0))) && (t2_x == 0.0)) && (((( !(t2_l0 != 0)) && ( !(t2_l1 != 0))) || ((t2_l0 != 0) && ( !(t2_l1 != 0)))) || (((t2_l1 != 0) && ( !(t2_l0 != 0))) || ((t2_l0 != 0) && (t2_l1 != 0))))) && (((( !(t2_evt0 != 0)) && ( !(t2_evt1 != 0))) || ((t2_evt0 != 0) && ( !(t2_evt1 != 0)))) || (((t2_evt1 != 0) && ( !(t2_evt0 != 0))) || ((t2_evt0 != 0) && (t2_evt1 != 0))))) && ((( !(t2_l0 != 0)) && ( !(t2_l1 != 0))) || (t2_x <= 5.0))) && ((((((( !(t1_l0 != 0)) && ( !(t1_l1 != 0))) && (t1_x == 0.0)) && (((( !(t1_l0 != 0)) && ( !(t1_l1 != 0))) || ((t1_l0 != 0) && ( !(t1_l1 != 0)))) || (((t1_l1 != 0) && ( !(t1_l0 != 0))) || ((t1_l0 != 0) && (t1_l1 != 0))))) && (((( !(t1_evt0 != 0)) && ( !(t1_evt1 != 0))) || ((t1_evt0 != 0) && ( !(t1_evt1 != 0)))) || (((t1_evt1 != 0) && ( !(t1_evt0 != 0))) || ((t1_evt0 != 0) && (t1_evt1 != 0))))) && ((( !(t1_l0 != 0)) && ( !(t1_l1 != 0))) || (t1_x <= 5.0))) && ((((((( !(t0_l0 != 0)) && ( !(t0_l1 != 0))) && (t0_x == 0.0)) && (((( !(t0_l0 != 0)) && ( !(t0_l1 != 0))) || ((t0_l0 != 0) && ( !(t0_l1 != 0)))) || (((t0_l1 != 0) && ( !(t0_l0 != 0))) || ((t0_l0 != 0) && (t0_l1 != 0))))) && (((( !(t0_evt0 != 0)) && ( !(t0_evt1 != 0))) || ((t0_evt0 != 0) && ( !(t0_evt1 != 0)))) || (((t0_evt1 != 0) && ( !(t0_evt0 != 0))) || ((t0_evt0 != 0) && (t0_evt1 != 0))))) && ((( !(t0_l0 != 0)) && ( !(t0_l1 != 0))) || (t0_x <= 5.0))) && (((((((( !(controller_l0 != 0)) && ( !(controller_l1 != 0))) && (controller_z == 0.0)) && (((( !(controller_l0 != 0)) && ( !(controller_l1 != 0))) || ((controller_l0 != 0) && ( !(controller_l1 != 0)))) || (((controller_l1 != 0) && ( !(controller_l0 != 0))) || ((controller_l0 != 0) && (controller_l1 != 0))))) && (((( !(controller_evt2 != 0)) && (( !(controller_evt0 != 0)) && ( !(controller_evt1 != 0)))) || (( !(controller_evt2 != 0)) && ((controller_evt0 != 0) && ( !(controller_evt1 != 0))))) || ((( !(controller_evt2 != 0)) && ((controller_evt1 != 0) && ( !(controller_evt0 != 0)))) || ((( !(controller_evt2 != 0)) && ((controller_evt0 != 0) && (controller_evt1 != 0))) || ((controller_evt2 != 0) && (( !(controller_evt0 != 0)) && ( !(controller_evt1 != 0)))))))) && (((((controller_cnt == 0) || (controller_cnt == 1)) || (controller_cnt == 2)) || (controller_cnt == 3)) || (controller_cnt == 4))) && ((controller_z <= 1.0) || ( !(((controller_l0 != 0) && ( !(controller_l1 != 0))) || ((controller_l0 != 0) && (controller_l1 != 0)))))) && (((((((( !(gate_l0 != 0)) && ( !(gate_l1 != 0))) && (gate_y == 0.0)) && (((( !(gate_l0 != 0)) && ( !(gate_l1 != 0))) || ((gate_l0 != 0) && ( !(gate_l1 != 0)))) || (((gate_l1 != 0) && ( !(gate_l0 != 0))) || ((gate_l0 != 0) && (gate_l1 != 0))))) && (((( !(gate_evt0 != 0)) && ( !(gate_evt1 != 0))) || ((gate_evt0 != 0) && ( !(gate_evt1 != 0)))) || (((gate_evt1 != 0) && ( !(gate_evt0 != 0))) || ((gate_evt0 != 0) && (gate_evt1 != 0))))) && ((gate_y <= 1.0) || ( !((gate_l0 != 0) && ( !(gate_l1 != 0)))))) && ((gate_y <= 2.0) || ( !((gate_l0 != 0) && (gate_l1 != 0))))) && (0.0 <= delta)))))) && (delta == _diverge_delta));
  while (__ok) {
    _x__diverge_delta = __VERIFIER_nondet_float();
    _x_t2_l1 = __VERIFIER_nondet_bool();
    _x_t2_l0 = __VERIFIER_nondet_bool();
    _x_t2_evt1 = __VERIFIER_nondet_bool();
    _x_t2_evt0 = __VERIFIER_nondet_bool();
    _x_t1_l1 = __VERIFIER_nondet_bool();
    _x_t1_l0 = __VERIFIER_nondet_bool();
    _x_t1_evt1 = __VERIFIER_nondet_bool();
    _x_t1_evt0 = __VERIFIER_nondet_bool();
    _x_t1_x = __VERIFIER_nondet_float();
    _x_t0_l1 = __VERIFIER_nondet_bool();
    _x_t0_evt1 = __VERIFIER_nondet_bool();
    _x_t0_evt0 = __VERIFIER_nondet_bool();
    _x_t0_x = __VERIFIER_nondet_float();
    _x_delta = __VERIFIER_nondet_float();
    _x_t2_x = __VERIFIER_nondet_float();
    _x_gate_l0 = __VERIFIER_nondet_bool();
    _x_controller_l0 = __VERIFIER_nondet_bool();
    _x_gate_l1 = __VERIFIER_nondet_bool();
    _x_gate_y = __VERIFIER_nondet_float();
    _x_controller_l1 = __VERIFIER_nondet_bool();
    _x_gate_evt0 = __VERIFIER_nondet_bool();
    _x_controller_evt0 = __VERIFIER_nondet_bool();
    _x_controller_evt1 = __VERIFIER_nondet_bool();
    _x_gate_evt1 = __VERIFIER_nondet_bool();
    _x_controller_z = __VERIFIER_nondet_float();
    _x_t0_l0 = __VERIFIER_nondet_bool();
    _x_controller_evt2 = __VERIFIER_nondet_bool();
    _x_controller_cnt = __VERIFIER_nondet_int();

    __ok = (((((((((((((((((((( !(_x_t2_l0 != 0)) && ( !(_x_t2_l1 != 0))) || ((_x_t2_l0 != 0) && ( !(_x_t2_l1 != 0)))) || (((_x_t2_l1 != 0) && ( !(_x_t2_l0 != 0))) || ((_x_t2_l0 != 0) && (_x_t2_l1 != 0)))) && (((( !(_x_t2_evt0 != 0)) && ( !(_x_t2_evt1 != 0))) || ((_x_t2_evt0 != 0) && ( !(_x_t2_evt1 != 0)))) || (((_x_t2_evt1 != 0) && ( !(_x_t2_evt0 != 0))) || ((_x_t2_evt0 != 0) && (_x_t2_evt1 != 0))))) && ((( !(_x_t2_l0 != 0)) && ( !(_x_t2_l1 != 0))) || (_x_t2_x <= 5.0))) && (((((t2_l0 != 0) == (_x_t2_l0 != 0)) && ((t2_l1 != 0) == (_x_t2_l1 != 0))) && ((delta + (t2_x + (-1.0 * _x_t2_x))) == 0.0)) || ( !(( !(delta <= 0.0)) || (( !(t2_evt0 != 0)) && ( !(t2_evt1 != 0))))))) && (((((_x_t2_l0 != 0) && ( !(_x_t2_l1 != 0))) && ((t2_evt0 != 0) && ( !(t2_evt1 != 0)))) && (_x_t2_x == 0.0)) || ( !((( !(t2_l0 != 0)) && ( !(t2_l1 != 0))) && ((delta == 0.0) && ( !(( !(t2_evt0 != 0)) && ( !(t2_evt1 != 0))))))))) && (((((_x_t2_l1 != 0) && ( !(_x_t2_l0 != 0))) && ( !(t2_x <= 2.0))) && (((t2_evt0 != 0) && (t2_evt1 != 0)) && (t2_x == _x_t2_x))) || ( !(((t2_l0 != 0) && ( !(t2_l1 != 0))) && ((delta == 0.0) && ( !(( !(t2_evt0 != 0)) && ( !(t2_evt1 != 0))))))))) && (((t2_x == _x_t2_x) && (((_x_t2_l0 != 0) && (_x_t2_l1 != 0)) && ((t2_evt0 != 0) && (t2_evt1 != 0)))) || ( !(((t2_l1 != 0) && ( !(t2_l0 != 0))) && ((delta == 0.0) && ( !(( !(t2_evt0 != 0)) && ( !(t2_evt1 != 0))))))))) && ((((( !(_x_t2_l0 != 0)) && ( !(_x_t2_l1 != 0))) && (t2_x <= 5.0)) && (((t2_evt1 != 0) && ( !(t2_evt0 != 0))) && (t2_x == _x_t2_x))) || ( !(((t2_l0 != 0) && (t2_l1 != 0)) && ((delta == 0.0) && ( !(( !(t2_evt0 != 0)) && ( !(t2_evt1 != 0))))))))) && (((((((((((( !(_x_t1_l0 != 0)) && ( !(_x_t1_l1 != 0))) || ((_x_t1_l0 != 0) && ( !(_x_t1_l1 != 0)))) || (((_x_t1_l1 != 0) && ( !(_x_t1_l0 != 0))) || ((_x_t1_l0 != 0) && (_x_t1_l1 != 0)))) && (((( !(_x_t1_evt0 != 0)) && ( !(_x_t1_evt1 != 0))) || ((_x_t1_evt0 != 0) && ( !(_x_t1_evt1 != 0)))) || (((_x_t1_evt1 != 0) && ( !(_x_t1_evt0 != 0))) || ((_x_t1_evt0 != 0) && (_x_t1_evt1 != 0))))) && ((( !(_x_t1_l0 != 0)) && ( !(_x_t1_l1 != 0))) || (_x_t1_x <= 5.0))) && (((((t1_l0 != 0) == (_x_t1_l0 != 0)) && ((t1_l1 != 0) == (_x_t1_l1 != 0))) && ((delta + (t1_x + (-1.0 * _x_t1_x))) == 0.0)) || ( !(( !(delta <= 0.0)) || (( !(t1_evt0 != 0)) && ( !(t1_evt1 != 0))))))) && (((((_x_t1_l0 != 0) && ( !(_x_t1_l1 != 0))) && ((t1_evt0 != 0) && ( !(t1_evt1 != 0)))) && (_x_t1_x == 0.0)) || ( !((( !(t1_l0 != 0)) && ( !(t1_l1 != 0))) && ((delta == 0.0) && ( !(( !(t1_evt0 != 0)) && ( !(t1_evt1 != 0))))))))) && (((((_x_t1_l1 != 0) && ( !(_x_t1_l0 != 0))) && ( !(t1_x <= 2.0))) && (((t1_evt0 != 0) && (t1_evt1 != 0)) && (t1_x == _x_t1_x))) || ( !(((t1_l0 != 0) && ( !(t1_l1 != 0))) && ((delta == 0.0) && ( !(( !(t1_evt0 != 0)) && ( !(t1_evt1 != 0))))))))) && (((t1_x == _x_t1_x) && (((_x_t1_l0 != 0) && (_x_t1_l1 != 0)) && ((t1_evt0 != 0) && (t1_evt1 != 0)))) || ( !(((t1_l1 != 0) && ( !(t1_l0 != 0))) && ((delta == 0.0) && ( !(( !(t1_evt0 != 0)) && ( !(t1_evt1 != 0))))))))) && ((((( !(_x_t1_l0 != 0)) && ( !(_x_t1_l1 != 0))) && (t1_x <= 5.0)) && (((t1_evt1 != 0) && ( !(t1_evt0 != 0))) && (t1_x == _x_t1_x))) || ( !(((t1_l0 != 0) && (t1_l1 != 0)) && ((delta == 0.0) && ( !(( !(t1_evt0 != 0)) && ( !(t1_evt1 != 0))))))))) && (((((((((((( !(_x_t0_l0 != 0)) && ( !(_x_t0_l1 != 0))) || ((_x_t0_l0 != 0) && ( !(_x_t0_l1 != 0)))) || (((_x_t0_l1 != 0) && ( !(_x_t0_l0 != 0))) || ((_x_t0_l0 != 0) && (_x_t0_l1 != 0)))) && (((( !(_x_t0_evt0 != 0)) && ( !(_x_t0_evt1 != 0))) || ((_x_t0_evt0 != 0) && ( !(_x_t0_evt1 != 0)))) || (((_x_t0_evt1 != 0) && ( !(_x_t0_evt0 != 0))) || ((_x_t0_evt0 != 0) && (_x_t0_evt1 != 0))))) && ((( !(_x_t0_l0 != 0)) && ( !(_x_t0_l1 != 0))) || (_x_t0_x <= 5.0))) && (((((t0_l0 != 0) == (_x_t0_l0 != 0)) && ((t0_l1 != 0) == (_x_t0_l1 != 0))) && ((delta + (t0_x + (-1.0 * _x_t0_x))) == 0.0)) || ( !(( !(delta <= 0.0)) || (( !(t0_evt0 != 0)) && ( !(t0_evt1 != 0))))))) && (((((_x_t0_l0 != 0) && ( !(_x_t0_l1 != 0))) && ((t0_evt0 != 0) && ( !(t0_evt1 != 0)))) && (_x_t0_x == 0.0)) || ( !((( !(t0_l0 != 0)) && ( !(t0_l1 != 0))) && ((delta == 0.0) && ( !(( !(t0_evt0 != 0)) && ( !(t0_evt1 != 0))))))))) && (((((_x_t0_l1 != 0) && ( !(_x_t0_l0 != 0))) && ( !(t0_x <= 2.0))) && (((t0_evt0 != 0) && (t0_evt1 != 0)) && (t0_x == _x_t0_x))) || ( !(((t0_l0 != 0) && ( !(t0_l1 != 0))) && ((delta == 0.0) && ( !(( !(t0_evt0 != 0)) && ( !(t0_evt1 != 0))))))))) && (((t0_x == _x_t0_x) && (((_x_t0_l0 != 0) && (_x_t0_l1 != 0)) && ((t0_evt0 != 0) && (t0_evt1 != 0)))) || ( !(((t0_l1 != 0) && ( !(t0_l0 != 0))) && ((delta == 0.0) && ( !(( !(t0_evt0 != 0)) && ( !(t0_evt1 != 0))))))))) && ((((( !(_x_t0_l0 != 0)) && ( !(_x_t0_l1 != 0))) && (t0_x <= 5.0)) && (((t0_evt1 != 0) && ( !(t0_evt0 != 0))) && (t0_x == _x_t0_x))) || ( !(((t0_l0 != 0) && (t0_l1 != 0)) && ((delta == 0.0) && ( !(( !(t0_evt0 != 0)) && ( !(t0_evt1 != 0))))))))) && (((((((((((((((((( !(_x_controller_l0 != 0)) && ( !(_x_controller_l1 != 0))) || ((_x_controller_l0 != 0) && ( !(_x_controller_l1 != 0)))) || (((_x_controller_l1 != 0) && ( !(_x_controller_l0 != 0))) || ((_x_controller_l0 != 0) && (_x_controller_l1 != 0)))) && (((( !(_x_controller_evt2 != 0)) && (( !(_x_controller_evt0 != 0)) && ( !(_x_controller_evt1 != 0)))) || (( !(_x_controller_evt2 != 0)) && ((_x_controller_evt0 != 0) && ( !(_x_controller_evt1 != 0))))) || ((( !(_x_controller_evt2 != 0)) && ((_x_controller_evt1 != 0) && ( !(_x_controller_evt0 != 0)))) || ((( !(_x_controller_evt2 != 0)) && ((_x_controller_evt0 != 0) && (_x_controller_evt1 != 0))) || ((_x_controller_evt2 != 0) && (( !(_x_controller_evt0 != 0)) && ( !(_x_controller_evt1 != 0)))))))) && (((((_x_controller_cnt == 0) || (_x_controller_cnt == 1)) || (_x_controller_cnt == 2)) || (_x_controller_cnt == 3)) || (_x_controller_cnt == 4))) && ((_x_controller_z <= 1.0) || ( !(((_x_controller_l0 != 0) && ( !(_x_controller_l1 != 0))) || ((_x_controller_l0 != 0) && (_x_controller_l1 != 0)))))) && ((((((controller_l0 != 0) == (_x_controller_l0 != 0)) && ((controller_l1 != 0) == (_x_controller_l1 != 0))) && ((delta + (controller_z + (-1.0 * _x_controller_z))) == 0.0)) && (controller_cnt == _x_controller_cnt)) || ( !(( !(delta <= 0.0)) || (( !(controller_evt2 != 0)) && (( !(controller_evt0 != 0)) && ( !(controller_evt1 != 0)))))))) && (((((_x_controller_l0 != 0) && ( !(_x_controller_l1 != 0))) && (( !(controller_evt2 != 0)) && ((controller_evt0 != 0) && ( !(controller_evt1 != 0))))) && ((_x_controller_cnt == 1) && (_x_controller_z == 0.0))) || ( !((( !(controller_l0 != 0)) && ( !(controller_l1 != 0))) && ((delta == 0.0) && ( !(( !(controller_evt2 != 0)) && (( !(controller_evt0 != 0)) && ( !(controller_evt1 != 0)))))))))) && (((controller_z == _x_controller_z) && (((_x_controller_l0 != 0) && ( !(_x_controller_l1 != 0))) || ((_x_controller_l1 != 0) && ( !(_x_controller_l0 != 0))))) || ( !(((controller_l0 != 0) && ( !(controller_l1 != 0))) && ((delta == 0.0) && ( !(( !(controller_evt2 != 0)) && (( !(controller_evt0 != 0)) && ( !(controller_evt1 != 0)))))))))) && ((((( !(controller_evt2 != 0)) && ((controller_evt0 != 0) && ( !(controller_evt1 != 0)))) && ((controller_cnt + (-1 * _x_controller_cnt)) == -1)) || ((( !(controller_evt2 != 0)) && ((controller_evt1 != 0) && ( !(controller_evt0 != 0)))) && ((controller_cnt + (-1 * _x_controller_cnt)) == 1))) || ( !(((delta == 0.0) && ( !(( !(controller_evt2 != 0)) && (( !(controller_evt0 != 0)) && ( !(controller_evt1 != 0)))))) && (((controller_l0 != 0) && ( !(controller_l1 != 0))) && ((_x_controller_l0 != 0) && ( !(_x_controller_l1 != 0)))))))) && (((( !(controller_evt2 != 0)) && ((controller_evt0 != 0) && (controller_evt1 != 0))) && ((controller_cnt == _x_controller_cnt) && (controller_z == 1.0))) || ( !(((delta == 0.0) && ( !(( !(controller_evt2 != 0)) && (( !(controller_evt0 != 0)) && ( !(controller_evt1 != 0)))))) && (((controller_l0 != 0) && ( !(controller_l1 != 0))) && ((_x_controller_l1 != 0) && ( !(_x_controller_l0 != 0)))))))) && ((((_x_controller_l1 != 0) && ( !(_x_controller_l0 != 0))) || ((_x_controller_l0 != 0) && (_x_controller_l1 != 0))) || ( !(((controller_l1 != 0) && ( !(controller_l0 != 0))) && ((delta == 0.0) && ( !(( !(controller_evt2 != 0)) && (( !(controller_evt0 != 0)) && ( !(controller_evt1 != 0)))))))))) && (((controller_z == _x_controller_z) && (((( !(controller_evt2 != 0)) && ((controller_evt0 != 0) && ( !(controller_evt1 != 0)))) && ((controller_cnt + (-1 * _x_controller_cnt)) == -1)) || (((( !(controller_evt2 != 0)) && ((controller_evt1 != 0) && ( !(controller_evt0 != 0)))) && ((controller_cnt + (-1 * _x_controller_cnt)) == 1)) && ( !(controller_cnt <= 1))))) || ( !(((delta == 0.0) && ( !(( !(controller_evt2 != 0)) && (( !(controller_evt0 != 0)) && ( !(controller_evt1 != 0)))))) && (((controller_l1 != 0) && ( !(controller_l0 != 0))) && ((_x_controller_l1 != 0) && ( !(_x_controller_l0 != 0)))))))) && ((((( !(controller_evt2 != 0)) && ((controller_evt1 != 0) && ( !(controller_evt0 != 0)))) && (controller_cnt == 1)) && ((_x_controller_cnt == 0) && (_x_controller_z == 0.0))) || ( !(((delta == 0.0) && ( !(( !(controller_evt2 != 0)) && (( !(controller_evt0 != 0)) && ( !(controller_evt1 != 0)))))) && (((controller_l1 != 0) && ( !(controller_l0 != 0))) && ((_x_controller_l0 != 0) && (_x_controller_l1 != 0))))))) && (((controller_z == _x_controller_z) && ((( !(_x_controller_l0 != 0)) && ( !(_x_controller_l1 != 0))) || ((_x_controller_l1 != 0) && ( !(_x_controller_l0 != 0))))) || ( !(((controller_l0 != 0) && (controller_l1 != 0)) && ((delta == 0.0) && ( !(( !(controller_evt2 != 0)) && (( !(controller_evt0 != 0)) && ( !(controller_evt1 != 0)))))))))) && ((((controller_cnt + (-1 * _x_controller_cnt)) == -1) && ((( !(controller_evt2 != 0)) && ((controller_evt0 != 0) && ( !(controller_evt1 != 0)))) && (controller_z <= 1.0))) || ( !(((delta == 0.0) && ( !(( !(controller_evt2 != 0)) && (( !(controller_evt0 != 0)) && ( !(controller_evt1 != 0)))))) && (((_x_controller_l1 != 0) && ( !(_x_controller_l0 != 0))) && ((controller_l0 != 0) && (controller_l1 != 0))))))) && ((((((((((((( !(_x_gate_l0 != 0)) && ( !(_x_gate_l1 != 0))) || ((_x_gate_l0 != 0) && ( !(_x_gate_l1 != 0)))) || (((_x_gate_l1 != 0) && ( !(_x_gate_l0 != 0))) || ((_x_gate_l0 != 0) && (_x_gate_l1 != 0)))) && (((( !(_x_gate_evt0 != 0)) && ( !(_x_gate_evt1 != 0))) || ((_x_gate_evt0 != 0) && ( !(_x_gate_evt1 != 0)))) || (((_x_gate_evt1 != 0) && ( !(_x_gate_evt0 != 0))) || ((_x_gate_evt0 != 0) && (_x_gate_evt1 != 0))))) && ((_x_gate_y <= 1.0) || ( !((_x_gate_l0 != 0) && ( !(_x_gate_l1 != 0)))))) && ((_x_gate_y <= 2.0) || ( !((_x_gate_l0 != 0) && (_x_gate_l1 != 0))))) && (((((gate_l0 != 0) == (_x_gate_l0 != 0)) && ((gate_l1 != 0) == (_x_gate_l1 != 0))) && ((delta + (gate_y + (-1.0 * _x_gate_y))) == 0.0)) || ( !((( !(gate_evt0 != 0)) && ( !(gate_evt1 != 0))) || ( !(delta <= 0.0)))))) && (((((_x_gate_l0 != 0) && ( !(_x_gate_l1 != 0))) && ((gate_evt0 != 0) && ( !(gate_evt1 != 0)))) && (_x_gate_y == 0.0)) || ( !((( !(gate_l0 != 0)) && ( !(gate_l1 != 0))) && ((delta == 0.0) && ( !(( !(gate_evt0 != 0)) && ( !(gate_evt1 != 0))))))))) && (((((_x_gate_l1 != 0) && ( !(_x_gate_l0 != 0))) && ((gate_evt0 != 0) && (gate_evt1 != 0))) && ((gate_y <= 1.0) && (gate_y == _x_gate_y))) || ( !(((gate_l0 != 0) && ( !(gate_l1 != 0))) && ((delta == 0.0) && ( !(( !(gate_evt0 != 0)) && ( !(gate_evt1 != 0))))))))) && (((_x_gate_y == 0.0) && (((_x_gate_l0 != 0) && (_x_gate_l1 != 0)) && ((gate_evt1 != 0) && ( !(gate_evt0 != 0))))) || ( !(((gate_l1 != 0) && ( !(gate_l0 != 0))) && ((delta == 0.0) && ( !(( !(gate_evt0 != 0)) && ( !(gate_evt1 != 0))))))))) && (((gate_y == _x_gate_y) && (((( !(_x_gate_l0 != 0)) && ( !(_x_gate_l1 != 0))) && (1.0 <= gate_y)) && (((gate_evt0 != 0) && (gate_evt1 != 0)) && (gate_y <= 2.0)))) || ( !(((gate_l0 != 0) && (gate_l1 != 0)) && ((delta == 0.0) && ( !(( !(gate_evt0 != 0)) && ( !(gate_evt1 != 0))))))))) && (0.0 <= _x_delta)))))) && ((( !(t2_evt0 != 0)) && ( !(t2_evt1 != 0))) || ( !((delta == 0.0) && ( !(( !(t0_evt0 != 0)) && ( !(t0_evt1 != 0)))))))) && ((( !(t2_evt0 != 0)) && ( !(t2_evt1 != 0))) || ( !((delta == 0.0) && ( !(( !(t1_evt0 != 0)) && ( !(t1_evt1 != 0)))))))) && ((( !(t1_evt0 != 0)) && ( !(t1_evt1 != 0))) || ( !((delta == 0.0) && ( !(( !(t2_evt0 != 0)) && ( !(t2_evt1 != 0)))))))) && ((((gate_evt0 != 0) && ( !(gate_evt1 != 0))) == (( !(controller_evt2 != 0)) && ((controller_evt0 != 0) && (controller_evt1 != 0)))) || ( !(delta == 0.0)))) && (( !(delta == 0.0)) || (((gate_evt1 != 0) && ( !(gate_evt0 != 0))) == ((controller_evt2 != 0) && (( !(controller_evt0 != 0)) && ( !(controller_evt1 != 0))))))) && (( !(delta == 0.0)) || ((( !(controller_evt2 != 0)) && ((controller_evt0 != 0) && ( !(controller_evt1 != 0)))) == (((t2_evt0 != 0) && ( !(t2_evt1 != 0))) || (((t0_evt0 != 0) && ( !(t0_evt1 != 0))) || ((t1_evt0 != 0) && ( !(t1_evt1 != 0)))))))) && (( !(delta == 0.0)) || ((( !(controller_evt2 != 0)) && ((controller_evt1 != 0) && ( !(controller_evt0 != 0)))) == (((t2_evt1 != 0) && ( !(t2_evt0 != 0))) || (((t0_evt1 != 0) && ( !(t0_evt0 != 0))) || ((t1_evt1 != 0) && ( !(t1_evt0 != 0)))))))) && (((delta == _x__diverge_delta) || ( !(1.0 <= _diverge_delta))) && ((1.0 <= _diverge_delta) || ((delta + (_diverge_delta + (-1.0 * _x__diverge_delta))) == 0.0))));
    _diverge_delta = _x__diverge_delta;
    t2_l1 = _x_t2_l1;
    t2_l0 = _x_t2_l0;
    t2_evt1 = _x_t2_evt1;
    t2_evt0 = _x_t2_evt0;
    t1_l1 = _x_t1_l1;
    t1_l0 = _x_t1_l0;
    t1_evt1 = _x_t1_evt1;
    t1_evt0 = _x_t1_evt0;
    t1_x = _x_t1_x;
    t0_l1 = _x_t0_l1;
    t0_evt1 = _x_t0_evt1;
    t0_evt0 = _x_t0_evt0;
    t0_x = _x_t0_x;
    delta = _x_delta;
    t2_x = _x_t2_x;
    gate_l0 = _x_gate_l0;
    controller_l0 = _x_controller_l0;
    gate_l1 = _x_gate_l1;
    gate_y = _x_gate_y;
    controller_l1 = _x_controller_l1;
    gate_evt0 = _x_gate_evt0;
    controller_evt0 = _x_controller_evt0;
    controller_evt1 = _x_controller_evt1;
    gate_evt1 = _x_gate_evt1;
    controller_z = _x_controller_z;
    t0_l0 = _x_t0_l0;
    controller_evt2 = _x_controller_evt2;
    controller_cnt = _x_controller_cnt;

  }
}
