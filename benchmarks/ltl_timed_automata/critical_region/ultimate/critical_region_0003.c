//@ ltl invariant negative: ( ( ([] (<> AP((id == 1)))) || (! ([] ( (! ( (! AP((pc0_l2 != 0))) && ( AP((pc0_l0 != 0)) && AP((pc0_l1 != 0))))) || (! ( (! AP((pc1_l2 != 0))) && ( AP((pc1_l0 != 0)) && AP((pc1_l1 != 0))))))))) || (! ([] (<> AP((1.0 <= _diverge_delta))))));

extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);

char __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}


char pc2_l2, _x_pc2_l2;
char pc2_l1, _x_pc2_l1;
char a1_evt1, _x_a1_evt1;
char a2_l, _x_a2_l;
char a1_evt0, _x_a1_evt0;
char pc1_l0, _x_pc1_l0;
char a0_evt1, _x_a0_evt1;
char pc2_l0, _x_pc2_l0;
char pc2_evt1, _x_pc2_evt1;
char a0_evt0, _x_a0_evt0;
char a1_l, _x_a1_l;
float delta, _x_delta;
char pc0_l2, _x_pc0_l2;
char pc2_evt0, _x_pc2_evt0;
float pc1_x, _x_pc1_x;
float pc0_x, _x_pc0_x;
char c_initial, _x_c_initial;
char pc0_evt0, _x_pc0_evt0;
char pc0_evt1, _x_pc0_evt1;
char pc0_l1, _x_pc0_l1;
char a0_l, _x_a0_l;
int id, _x_id;
char pc1_evt0, _x_pc1_evt0;
char c_move, _x_c_move;
char pc1_evt1, _x_pc1_evt1;
char a2_evt0, _x_a2_evt0;
char pc1_l1, _x_pc1_l1;
char a2_evt1, _x_a2_evt1;
char pc0_l0, _x_pc0_l0;
char pc1_l2, _x_pc1_l2;
float _diverge_delta, _x__diverge_delta;
float pc2_x, _x_pc2_x;

int main()
{
  pc2_l2 = __VERIFIER_nondet_bool();
  pc2_l1 = __VERIFIER_nondet_bool();
  a1_evt1 = __VERIFIER_nondet_bool();
  a2_l = __VERIFIER_nondet_bool();
  a1_evt0 = __VERIFIER_nondet_bool();
  pc1_l0 = __VERIFIER_nondet_bool();
  a0_evt1 = __VERIFIER_nondet_bool();
  pc2_l0 = __VERIFIER_nondet_bool();
  pc2_evt1 = __VERIFIER_nondet_bool();
  a0_evt0 = __VERIFIER_nondet_bool();
  a1_l = __VERIFIER_nondet_bool();
  delta = __VERIFIER_nondet_float();
  pc0_l2 = __VERIFIER_nondet_bool();
  pc2_evt0 = __VERIFIER_nondet_bool();
  pc1_x = __VERIFIER_nondet_float();
  pc0_x = __VERIFIER_nondet_float();
  c_initial = __VERIFIER_nondet_bool();
  pc0_evt0 = __VERIFIER_nondet_bool();
  pc0_evt1 = __VERIFIER_nondet_bool();
  pc0_l1 = __VERIFIER_nondet_bool();
  a0_l = __VERIFIER_nondet_bool();
  id = __VERIFIER_nondet_int();
  pc1_evt0 = __VERIFIER_nondet_bool();
  c_move = __VERIFIER_nondet_bool();
  pc1_evt1 = __VERIFIER_nondet_bool();
  a2_evt0 = __VERIFIER_nondet_bool();
  pc1_l1 = __VERIFIER_nondet_bool();
  a2_evt1 = __VERIFIER_nondet_bool();
  pc0_l0 = __VERIFIER_nondet_bool();
  pc1_l2 = __VERIFIER_nondet_bool();
  _diverge_delta = __VERIFIER_nondet_float();
  pc2_x = __VERIFIER_nondet_float();

  int __ok = (((((((( !(pc2_l2 != 0)) && (( !(pc2_l0 != 0)) && ( !(pc2_l1 != 0)))) && (pc2_x == 0.0)) && (((( !(pc2_evt0 != 0)) && ( !(pc2_evt1 != 0))) || ((pc2_evt1 != 0) && ( !(pc2_evt0 != 0)))) || (((pc2_evt0 != 0) && ( !(pc2_evt1 != 0))) || ((pc2_evt0 != 0) && (pc2_evt1 != 0))))) && ((( !(pc2_l2 != 0)) && ((pc2_l0 != 0) && (pc2_l1 != 0))) || ((((( !(pc2_l2 != 0)) && (( !(pc2_l0 != 0)) && ( !(pc2_l1 != 0)))) || ((pc2_l2 != 0) && (( !(pc2_l0 != 0)) && ( !(pc2_l1 != 0))))) || ((( !(pc2_l2 != 0)) && ((pc2_l1 != 0) && ( !(pc2_l0 != 0)))) || ((pc2_l2 != 0) && ((pc2_l1 != 0) && ( !(pc2_l0 != 0)))))) || ((( !(pc2_l2 != 0)) && ((pc2_l0 != 0) && ( !(pc2_l1 != 0)))) || ((pc2_l2 != 0) && ((pc2_l0 != 0) && ( !(pc2_l1 != 0)))))))) && (((((( !(pc1_l2 != 0)) && (( !(pc1_l0 != 0)) && ( !(pc1_l1 != 0)))) && (pc1_x == 0.0)) && (((( !(pc1_evt0 != 0)) && ( !(pc1_evt1 != 0))) || ((pc1_evt1 != 0) && ( !(pc1_evt0 != 0)))) || (((pc1_evt0 != 0) && ( !(pc1_evt1 != 0))) || ((pc1_evt0 != 0) && (pc1_evt1 != 0))))) && ((( !(pc1_l2 != 0)) && ((pc1_l0 != 0) && (pc1_l1 != 0))) || ((((( !(pc1_l2 != 0)) && (( !(pc1_l0 != 0)) && ( !(pc1_l1 != 0)))) || ((pc1_l2 != 0) && (( !(pc1_l0 != 0)) && ( !(pc1_l1 != 0))))) || ((( !(pc1_l2 != 0)) && ((pc1_l1 != 0) && ( !(pc1_l0 != 0)))) || ((pc1_l2 != 0) && ((pc1_l1 != 0) && ( !(pc1_l0 != 0)))))) || ((( !(pc1_l2 != 0)) && ((pc1_l0 != 0) && ( !(pc1_l1 != 0)))) || ((pc1_l2 != 0) && ((pc1_l0 != 0) && ( !(pc1_l1 != 0)))))))) && (((((( !(pc0_l2 != 0)) && (( !(pc0_l0 != 0)) && ( !(pc0_l1 != 0)))) && (pc0_x == 0.0)) && (((( !(pc0_evt0 != 0)) && ( !(pc0_evt1 != 0))) || ((pc0_evt1 != 0) && ( !(pc0_evt0 != 0)))) || (((pc0_evt0 != 0) && ( !(pc0_evt1 != 0))) || ((pc0_evt0 != 0) && (pc0_evt1 != 0))))) && ((( !(pc0_l2 != 0)) && ((pc0_l0 != 0) && (pc0_l1 != 0))) || ((((( !(pc0_l2 != 0)) && (( !(pc0_l0 != 0)) && ( !(pc0_l1 != 0)))) || ((pc0_l2 != 0) && (( !(pc0_l0 != 0)) && ( !(pc0_l1 != 0))))) || ((( !(pc0_l2 != 0)) && ((pc0_l1 != 0) && ( !(pc0_l0 != 0)))) || ((pc0_l2 != 0) && ((pc0_l1 != 0) && ( !(pc0_l0 != 0)))))) || ((( !(pc0_l2 != 0)) && ((pc0_l0 != 0) && ( !(pc0_l1 != 0)))) || ((pc0_l2 != 0) && ((pc0_l0 != 0) && ( !(pc0_l1 != 0)))))))) && ((( !(a2_l != 0)) && ((( !(a2_evt0 != 0)) && ( !(a2_evt1 != 0))) || (((a2_evt1 != 0) && ( !(a2_evt0 != 0))) || ((a2_evt0 != 0) && ( !(a2_evt1 != 0)))))) && ((( !(a1_l != 0)) && ((( !(a1_evt0 != 0)) && ( !(a1_evt1 != 0))) || (((a1_evt1 != 0) && ( !(a1_evt0 != 0))) || ((a1_evt0 != 0) && ( !(a1_evt1 != 0)))))) && ((( !(a0_l != 0)) && ((( !(a0_evt0 != 0)) && ( !(a0_evt1 != 0))) || (((a0_evt1 != 0) && ( !(a0_evt0 != 0))) || ((a0_evt0 != 0) && ( !(a0_evt1 != 0)))))) && ((c_initial != 0) && (0.0 <= delta)))))))) && ((id == 2) || ((id == 0) || (id == 1)))) && (delta == _diverge_delta));
  while (__ok) {
    _x_pc2_l2 = __VERIFIER_nondet_bool();
    _x_pc2_l1 = __VERIFIER_nondet_bool();
    _x_a1_evt1 = __VERIFIER_nondet_bool();
    _x_a2_l = __VERIFIER_nondet_bool();
    _x_a1_evt0 = __VERIFIER_nondet_bool();
    _x_pc1_l0 = __VERIFIER_nondet_bool();
    _x_a0_evt1 = __VERIFIER_nondet_bool();
    _x_pc2_l0 = __VERIFIER_nondet_bool();
    _x_pc2_evt1 = __VERIFIER_nondet_bool();
    _x_a0_evt0 = __VERIFIER_nondet_bool();
    _x_a1_l = __VERIFIER_nondet_bool();
    _x_delta = __VERIFIER_nondet_float();
    _x_pc0_l2 = __VERIFIER_nondet_bool();
    _x_pc2_evt0 = __VERIFIER_nondet_bool();
    _x_pc1_x = __VERIFIER_nondet_float();
    _x_pc0_x = __VERIFIER_nondet_float();
    _x_c_initial = __VERIFIER_nondet_bool();
    _x_pc0_evt0 = __VERIFIER_nondet_bool();
    _x_pc0_evt1 = __VERIFIER_nondet_bool();
    _x_pc0_l1 = __VERIFIER_nondet_bool();
    _x_a0_l = __VERIFIER_nondet_bool();
    _x_id = __VERIFIER_nondet_int();
    _x_pc1_evt0 = __VERIFIER_nondet_bool();
    _x_c_move = __VERIFIER_nondet_bool();
    _x_pc1_evt1 = __VERIFIER_nondet_bool();
    _x_a2_evt0 = __VERIFIER_nondet_bool();
    _x_pc1_l1 = __VERIFIER_nondet_bool();
    _x_a2_evt1 = __VERIFIER_nondet_bool();
    _x_pc0_l0 = __VERIFIER_nondet_bool();
    _x_pc1_l2 = __VERIFIER_nondet_bool();
    _x__diverge_delta = __VERIFIER_nondet_float();
    _x_pc2_x = __VERIFIER_nondet_float();

    __ok = (((((((((((((((((((((((((((((( !(_x_pc2_evt0 != 0)) && ( !(_x_pc2_evt1 != 0))) || ((_x_pc2_evt1 != 0) && ( !(_x_pc2_evt0 != 0)))) || (((_x_pc2_evt0 != 0) && ( !(_x_pc2_evt1 != 0))) || ((_x_pc2_evt0 != 0) && (_x_pc2_evt1 != 0)))) && ((( !(_x_pc2_l2 != 0)) && ((_x_pc2_l0 != 0) && (_x_pc2_l1 != 0))) || ((((( !(_x_pc2_l2 != 0)) && (( !(_x_pc2_l0 != 0)) && ( !(_x_pc2_l1 != 0)))) || ((_x_pc2_l2 != 0) && (( !(_x_pc2_l0 != 0)) && ( !(_x_pc2_l1 != 0))))) || ((( !(_x_pc2_l2 != 0)) && ((_x_pc2_l1 != 0) && ( !(_x_pc2_l0 != 0)))) || ((_x_pc2_l2 != 0) && ((_x_pc2_l1 != 0) && ( !(_x_pc2_l0 != 0)))))) || ((( !(_x_pc2_l2 != 0)) && ((_x_pc2_l0 != 0) && ( !(_x_pc2_l1 != 0)))) || ((_x_pc2_l2 != 0) && ((_x_pc2_l0 != 0) && ( !(_x_pc2_l1 != 0)))))))) && ((delta <= 0.0) || (((((pc2_l0 != 0) == (_x_pc2_l0 != 0)) && ((pc2_l1 != 0) == (_x_pc2_l1 != 0))) && ((pc2_l2 != 0) == (_x_pc2_l2 != 0))) && ((delta + (pc2_x + (-1.0 * _x_pc2_x))) == 0.0)))) && ((((((pc2_l0 != 0) == (_x_pc2_l0 != 0)) && ((pc2_l1 != 0) == (_x_pc2_l1 != 0))) && ((pc2_l2 != 0) == (_x_pc2_l2 != 0))) && ((delta + (pc2_x + (-1.0 * _x_pc2_x))) == 0.0)) || ( !(( !(pc2_evt0 != 0)) && ( !(pc2_evt1 != 0)))))) && (((((pc2_evt0 != 0) && (pc2_evt1 != 0)) && (pc2_x <= 50.0)) && (((_x_pc2_l2 != 0) && (( !(_x_pc2_l0 != 0)) && ( !(_x_pc2_l1 != 0)))) && (_x_pc2_x == 0.0))) || ( !((( !(pc2_l2 != 0)) && (( !(pc2_l0 != 0)) && ( !(pc2_l1 != 0)))) && ((delta == 0.0) && ( !(( !(pc2_evt0 != 0)) && ( !(pc2_evt1 != 0))))))))) && ((((pc2_evt0 != 0) && (pc2_evt1 != 0)) && ((( !(_x_pc2_l2 != 0)) && (( !(_x_pc2_l0 != 0)) && ( !(_x_pc2_l1 != 0)))) || (( !(_x_pc2_l2 != 0)) && ((_x_pc2_l1 != 0) && ( !(_x_pc2_l0 != 0)))))) || ( !(((pc2_l2 != 0) && (( !(pc2_l0 != 0)) && ( !(pc2_l1 != 0)))) && ((delta == 0.0) && ( !(( !(pc2_evt0 != 0)) && ( !(pc2_evt1 != 0))))))))) && (((_x_pc2_x == 0.0) && (25.0 <= pc2_x)) || ( !((( !(_x_pc2_l2 != 0)) && (( !(_x_pc2_l0 != 0)) && ( !(_x_pc2_l1 != 0)))) && ((pc2_l2 != 0) && (( !(pc2_l0 != 0)) && ( !(pc2_l1 != 0)))))))) && (((pc2_x <= 24.0) && (pc2_x == _x_pc2_x)) || ( !(((pc2_l2 != 0) && (( !(pc2_l0 != 0)) && ( !(pc2_l1 != 0)))) && (( !(_x_pc2_l2 != 0)) && ((_x_pc2_l1 != 0) && ( !(_x_pc2_l0 != 0)))))))) && (((_x_pc2_x == 0.0) && (((pc2_evt1 != 0) && ( !(pc2_evt0 != 0))) && ((_x_pc2_l2 != 0) && ((_x_pc2_l1 != 0) && ( !(_x_pc2_l0 != 0)))))) || ( !((( !(pc2_l2 != 0)) && ((pc2_l1 != 0) && ( !(pc2_l0 != 0)))) && ((delta == 0.0) && ( !(( !(pc2_evt0 != 0)) && ( !(pc2_evt1 != 0))))))))) && (((( !(_x_pc2_l2 != 0)) && ((_x_pc2_l0 != 0) && ( !(_x_pc2_l1 != 0)))) || (( !(_x_pc2_l2 != 0)) && ((_x_pc2_l0 != 0) && (_x_pc2_l1 != 0)))) || ( !(((pc2_l2 != 0) && ((pc2_l1 != 0) && ( !(pc2_l0 != 0)))) && ((delta == 0.0) && ( !(( !(pc2_evt0 != 0)) && ( !(pc2_evt1 != 0))))))))) && (((pc2_x == _x_pc2_x) && (((pc2_evt0 != 0) && (pc2_evt1 != 0)) && (50.0 <= pc2_x))) || ( !(((pc2_l2 != 0) && ((pc2_l1 != 0) && ( !(pc2_l0 != 0)))) && (( !(_x_pc2_l2 != 0)) && ((_x_pc2_l0 != 0) && (_x_pc2_l1 != 0))))))) && (((_x_pc2_x == 0.0) && (((pc2_evt0 != 0) && ( !(pc2_evt1 != 0))) && (pc2_x <= 25.0))) || ( !(((pc2_l2 != 0) && ((pc2_l1 != 0) && ( !(pc2_l0 != 0)))) && (( !(_x_pc2_l2 != 0)) && ((_x_pc2_l0 != 0) && ( !(_x_pc2_l1 != 0)))))))) && (((((pc2_evt0 != 0) && (pc2_evt1 != 0)) && (pc2_x == _x_pc2_x)) && (((_x_pc2_l2 != 0) && ((_x_pc2_l0 != 0) && ( !(_x_pc2_l1 != 0)))) || (( !(_x_pc2_l2 != 0)) && ((_x_pc2_l0 != 0) && (_x_pc2_l1 != 0))))) || ( !((( !(pc2_l2 != 0)) && ((pc2_l0 != 0) && ( !(pc2_l1 != 0)))) && ((delta == 0.0) && ( !(( !(pc2_evt0 != 0)) && ( !(pc2_evt1 != 0))))))))) && ((25.0 <= pc2_x) || ( !((( !(pc2_l2 != 0)) && ((pc2_l0 != 0) && ( !(pc2_l1 != 0)))) && (( !(_x_pc2_l2 != 0)) && ((_x_pc2_l0 != 0) && (_x_pc2_l1 != 0))))))) && ((pc2_x <= 24.0) || ( !((( !(pc2_l2 != 0)) && ((pc2_l0 != 0) && ( !(pc2_l1 != 0)))) && ((_x_pc2_l2 != 0) && ((_x_pc2_l0 != 0) && ( !(_x_pc2_l1 != 0)))))))) && ((( !(_x_pc2_l2 != 0)) && ((_x_pc2_l0 != 0) && (_x_pc2_l1 != 0))) || ( !((( !(pc2_l2 != 0)) && ((pc2_l0 != 0) && (pc2_l1 != 0))) && ((delta == 0.0) && ( !(( !(pc2_evt0 != 0)) && ( !(pc2_evt1 != 0))))))))) && ((( !(_x_pc2_l2 != 0)) && (( !(_x_pc2_l0 != 0)) && ( !(_x_pc2_l1 != 0)))) || ( !(((pc2_l2 != 0) && ((pc2_l0 != 0) && ( !(pc2_l1 != 0)))) && ((delta == 0.0) && ( !(( !(pc2_evt0 != 0)) && ( !(pc2_evt1 != 0))))))))) && ((((((((((((((((((((( !(_x_pc1_evt0 != 0)) && ( !(_x_pc1_evt1 != 0))) || ((_x_pc1_evt1 != 0) && ( !(_x_pc1_evt0 != 0)))) || (((_x_pc1_evt0 != 0) && ( !(_x_pc1_evt1 != 0))) || ((_x_pc1_evt0 != 0) && (_x_pc1_evt1 != 0)))) && ((( !(_x_pc1_l2 != 0)) && ((_x_pc1_l0 != 0) && (_x_pc1_l1 != 0))) || ((((( !(_x_pc1_l2 != 0)) && (( !(_x_pc1_l0 != 0)) && ( !(_x_pc1_l1 != 0)))) || ((_x_pc1_l2 != 0) && (( !(_x_pc1_l0 != 0)) && ( !(_x_pc1_l1 != 0))))) || ((( !(_x_pc1_l2 != 0)) && ((_x_pc1_l1 != 0) && ( !(_x_pc1_l0 != 0)))) || ((_x_pc1_l2 != 0) && ((_x_pc1_l1 != 0) && ( !(_x_pc1_l0 != 0)))))) || ((( !(_x_pc1_l2 != 0)) && ((_x_pc1_l0 != 0) && ( !(_x_pc1_l1 != 0)))) || ((_x_pc1_l2 != 0) && ((_x_pc1_l0 != 0) && ( !(_x_pc1_l1 != 0)))))))) && ((delta <= 0.0) || (((((pc1_l0 != 0) == (_x_pc1_l0 != 0)) && ((pc1_l1 != 0) == (_x_pc1_l1 != 0))) && ((pc1_l2 != 0) == (_x_pc1_l2 != 0))) && ((delta + (pc1_x + (-1.0 * _x_pc1_x))) == 0.0)))) && ((((((pc1_l0 != 0) == (_x_pc1_l0 != 0)) && ((pc1_l1 != 0) == (_x_pc1_l1 != 0))) && ((pc1_l2 != 0) == (_x_pc1_l2 != 0))) && ((delta + (pc1_x + (-1.0 * _x_pc1_x))) == 0.0)) || ( !(( !(pc1_evt0 != 0)) && ( !(pc1_evt1 != 0)))))) && (((((pc1_evt0 != 0) && (pc1_evt1 != 0)) && (pc1_x <= 50.0)) && (((_x_pc1_l2 != 0) && (( !(_x_pc1_l0 != 0)) && ( !(_x_pc1_l1 != 0)))) && (_x_pc1_x == 0.0))) || ( !((( !(pc1_l2 != 0)) && (( !(pc1_l0 != 0)) && ( !(pc1_l1 != 0)))) && ((delta == 0.0) && ( !(( !(pc1_evt0 != 0)) && ( !(pc1_evt1 != 0))))))))) && ((((pc1_evt0 != 0) && (pc1_evt1 != 0)) && ((( !(_x_pc1_l2 != 0)) && (( !(_x_pc1_l0 != 0)) && ( !(_x_pc1_l1 != 0)))) || (( !(_x_pc1_l2 != 0)) && ((_x_pc1_l1 != 0) && ( !(_x_pc1_l0 != 0)))))) || ( !(((pc1_l2 != 0) && (( !(pc1_l0 != 0)) && ( !(pc1_l1 != 0)))) && ((delta == 0.0) && ( !(( !(pc1_evt0 != 0)) && ( !(pc1_evt1 != 0))))))))) && (((_x_pc1_x == 0.0) && (25.0 <= pc1_x)) || ( !((( !(_x_pc1_l2 != 0)) && (( !(_x_pc1_l0 != 0)) && ( !(_x_pc1_l1 != 0)))) && ((pc1_l2 != 0) && (( !(pc1_l0 != 0)) && ( !(pc1_l1 != 0)))))))) && (((pc1_x <= 24.0) && (pc1_x == _x_pc1_x)) || ( !(((pc1_l2 != 0) && (( !(pc1_l0 != 0)) && ( !(pc1_l1 != 0)))) && (( !(_x_pc1_l2 != 0)) && ((_x_pc1_l1 != 0) && ( !(_x_pc1_l0 != 0)))))))) && (((_x_pc1_x == 0.0) && (((pc1_evt1 != 0) && ( !(pc1_evt0 != 0))) && ((_x_pc1_l2 != 0) && ((_x_pc1_l1 != 0) && ( !(_x_pc1_l0 != 0)))))) || ( !((( !(pc1_l2 != 0)) && ((pc1_l1 != 0) && ( !(pc1_l0 != 0)))) && ((delta == 0.0) && ( !(( !(pc1_evt0 != 0)) && ( !(pc1_evt1 != 0))))))))) && (((( !(_x_pc1_l2 != 0)) && ((_x_pc1_l0 != 0) && ( !(_x_pc1_l1 != 0)))) || (( !(_x_pc1_l2 != 0)) && ((_x_pc1_l0 != 0) && (_x_pc1_l1 != 0)))) || ( !(((pc1_l2 != 0) && ((pc1_l1 != 0) && ( !(pc1_l0 != 0)))) && ((delta == 0.0) && ( !(( !(pc1_evt0 != 0)) && ( !(pc1_evt1 != 0))))))))) && (((pc1_x == _x_pc1_x) && (((pc1_evt0 != 0) && (pc1_evt1 != 0)) && (50.0 <= pc1_x))) || ( !(((pc1_l2 != 0) && ((pc1_l1 != 0) && ( !(pc1_l0 != 0)))) && (( !(_x_pc1_l2 != 0)) && ((_x_pc1_l0 != 0) && (_x_pc1_l1 != 0))))))) && (((_x_pc1_x == 0.0) && (((pc1_evt0 != 0) && ( !(pc1_evt1 != 0))) && (pc1_x <= 25.0))) || ( !(((pc1_l2 != 0) && ((pc1_l1 != 0) && ( !(pc1_l0 != 0)))) && (( !(_x_pc1_l2 != 0)) && ((_x_pc1_l0 != 0) && ( !(_x_pc1_l1 != 0)))))))) && (((((pc1_evt0 != 0) && (pc1_evt1 != 0)) && (pc1_x == _x_pc1_x)) && (((_x_pc1_l2 != 0) && ((_x_pc1_l0 != 0) && ( !(_x_pc1_l1 != 0)))) || (( !(_x_pc1_l2 != 0)) && ((_x_pc1_l0 != 0) && (_x_pc1_l1 != 0))))) || ( !((( !(pc1_l2 != 0)) && ((pc1_l0 != 0) && ( !(pc1_l1 != 0)))) && ((delta == 0.0) && ( !(( !(pc1_evt0 != 0)) && ( !(pc1_evt1 != 0))))))))) && ((25.0 <= pc1_x) || ( !((( !(pc1_l2 != 0)) && ((pc1_l0 != 0) && ( !(pc1_l1 != 0)))) && (( !(_x_pc1_l2 != 0)) && ((_x_pc1_l0 != 0) && (_x_pc1_l1 != 0))))))) && ((pc1_x <= 24.0) || ( !((( !(pc1_l2 != 0)) && ((pc1_l0 != 0) && ( !(pc1_l1 != 0)))) && ((_x_pc1_l2 != 0) && ((_x_pc1_l0 != 0) && ( !(_x_pc1_l1 != 0)))))))) && ((( !(_x_pc1_l2 != 0)) && ((_x_pc1_l0 != 0) && (_x_pc1_l1 != 0))) || ( !((( !(pc1_l2 != 0)) && ((pc1_l0 != 0) && (pc1_l1 != 0))) && ((delta == 0.0) && ( !(( !(pc1_evt0 != 0)) && ( !(pc1_evt1 != 0))))))))) && ((( !(_x_pc1_l2 != 0)) && (( !(_x_pc1_l0 != 0)) && ( !(_x_pc1_l1 != 0)))) || ( !(((pc1_l2 != 0) && ((pc1_l0 != 0) && ( !(pc1_l1 != 0)))) && ((delta == 0.0) && ( !(( !(pc1_evt0 != 0)) && ( !(pc1_evt1 != 0))))))))) && ((((((((((((((((((((( !(_x_pc0_evt0 != 0)) && ( !(_x_pc0_evt1 != 0))) || ((_x_pc0_evt1 != 0) && ( !(_x_pc0_evt0 != 0)))) || (((_x_pc0_evt0 != 0) && ( !(_x_pc0_evt1 != 0))) || ((_x_pc0_evt0 != 0) && (_x_pc0_evt1 != 0)))) && ((( !(_x_pc0_l2 != 0)) && ((_x_pc0_l0 != 0) && (_x_pc0_l1 != 0))) || ((((( !(_x_pc0_l2 != 0)) && (( !(_x_pc0_l0 != 0)) && ( !(_x_pc0_l1 != 0)))) || ((_x_pc0_l2 != 0) && (( !(_x_pc0_l0 != 0)) && ( !(_x_pc0_l1 != 0))))) || ((( !(_x_pc0_l2 != 0)) && ((_x_pc0_l1 != 0) && ( !(_x_pc0_l0 != 0)))) || ((_x_pc0_l2 != 0) && ((_x_pc0_l1 != 0) && ( !(_x_pc0_l0 != 0)))))) || ((( !(_x_pc0_l2 != 0)) && ((_x_pc0_l0 != 0) && ( !(_x_pc0_l1 != 0)))) || ((_x_pc0_l2 != 0) && ((_x_pc0_l0 != 0) && ( !(_x_pc0_l1 != 0)))))))) && ((delta <= 0.0) || (((((pc0_l0 != 0) == (_x_pc0_l0 != 0)) && ((pc0_l1 != 0) == (_x_pc0_l1 != 0))) && ((pc0_l2 != 0) == (_x_pc0_l2 != 0))) && ((delta + (pc0_x + (-1.0 * _x_pc0_x))) == 0.0)))) && ((((((pc0_l0 != 0) == (_x_pc0_l0 != 0)) && ((pc0_l1 != 0) == (_x_pc0_l1 != 0))) && ((pc0_l2 != 0) == (_x_pc0_l2 != 0))) && ((delta + (pc0_x + (-1.0 * _x_pc0_x))) == 0.0)) || ( !(( !(pc0_evt0 != 0)) && ( !(pc0_evt1 != 0)))))) && (((((pc0_evt0 != 0) && (pc0_evt1 != 0)) && (pc0_x <= 50.0)) && (((_x_pc0_l2 != 0) && (( !(_x_pc0_l0 != 0)) && ( !(_x_pc0_l1 != 0)))) && (_x_pc0_x == 0.0))) || ( !((( !(pc0_l2 != 0)) && (( !(pc0_l0 != 0)) && ( !(pc0_l1 != 0)))) && ((delta == 0.0) && ( !(( !(pc0_evt0 != 0)) && ( !(pc0_evt1 != 0))))))))) && ((((pc0_evt0 != 0) && (pc0_evt1 != 0)) && ((( !(_x_pc0_l2 != 0)) && (( !(_x_pc0_l0 != 0)) && ( !(_x_pc0_l1 != 0)))) || (( !(_x_pc0_l2 != 0)) && ((_x_pc0_l1 != 0) && ( !(_x_pc0_l0 != 0)))))) || ( !(((pc0_l2 != 0) && (( !(pc0_l0 != 0)) && ( !(pc0_l1 != 0)))) && ((delta == 0.0) && ( !(( !(pc0_evt0 != 0)) && ( !(pc0_evt1 != 0))))))))) && (((_x_pc0_x == 0.0) && (25.0 <= pc0_x)) || ( !((( !(_x_pc0_l2 != 0)) && (( !(_x_pc0_l0 != 0)) && ( !(_x_pc0_l1 != 0)))) && ((pc0_l2 != 0) && (( !(pc0_l0 != 0)) && ( !(pc0_l1 != 0)))))))) && (((pc0_x <= 24.0) && (pc0_x == _x_pc0_x)) || ( !(((pc0_l2 != 0) && (( !(pc0_l0 != 0)) && ( !(pc0_l1 != 0)))) && (( !(_x_pc0_l2 != 0)) && ((_x_pc0_l1 != 0) && ( !(_x_pc0_l0 != 0)))))))) && (((_x_pc0_x == 0.0) && (((pc0_evt1 != 0) && ( !(pc0_evt0 != 0))) && ((_x_pc0_l2 != 0) && ((_x_pc0_l1 != 0) && ( !(_x_pc0_l0 != 0)))))) || ( !((( !(pc0_l2 != 0)) && ((pc0_l1 != 0) && ( !(pc0_l0 != 0)))) && ((delta == 0.0) && ( !(( !(pc0_evt0 != 0)) && ( !(pc0_evt1 != 0))))))))) && (((( !(_x_pc0_l2 != 0)) && ((_x_pc0_l0 != 0) && ( !(_x_pc0_l1 != 0)))) || (( !(_x_pc0_l2 != 0)) && ((_x_pc0_l0 != 0) && (_x_pc0_l1 != 0)))) || ( !(((pc0_l2 != 0) && ((pc0_l1 != 0) && ( !(pc0_l0 != 0)))) && ((delta == 0.0) && ( !(( !(pc0_evt0 != 0)) && ( !(pc0_evt1 != 0))))))))) && (((pc0_x == _x_pc0_x) && (((pc0_evt0 != 0) && (pc0_evt1 != 0)) && (50.0 <= pc0_x))) || ( !(((pc0_l2 != 0) && ((pc0_l1 != 0) && ( !(pc0_l0 != 0)))) && (( !(_x_pc0_l2 != 0)) && ((_x_pc0_l0 != 0) && (_x_pc0_l1 != 0))))))) && (((_x_pc0_x == 0.0) && (((pc0_evt0 != 0) && ( !(pc0_evt1 != 0))) && (pc0_x <= 25.0))) || ( !(((pc0_l2 != 0) && ((pc0_l1 != 0) && ( !(pc0_l0 != 0)))) && (( !(_x_pc0_l2 != 0)) && ((_x_pc0_l0 != 0) && ( !(_x_pc0_l1 != 0)))))))) && (((((pc0_evt0 != 0) && (pc0_evt1 != 0)) && (pc0_x == _x_pc0_x)) && (((_x_pc0_l2 != 0) && ((_x_pc0_l0 != 0) && ( !(_x_pc0_l1 != 0)))) || (( !(_x_pc0_l2 != 0)) && ((_x_pc0_l0 != 0) && (_x_pc0_l1 != 0))))) || ( !((( !(pc0_l2 != 0)) && ((pc0_l0 != 0) && ( !(pc0_l1 != 0)))) && ((delta == 0.0) && ( !(( !(pc0_evt0 != 0)) && ( !(pc0_evt1 != 0))))))))) && ((25.0 <= pc0_x) || ( !((( !(pc0_l2 != 0)) && ((pc0_l0 != 0) && ( !(pc0_l1 != 0)))) && (( !(_x_pc0_l2 != 0)) && ((_x_pc0_l0 != 0) && (_x_pc0_l1 != 0))))))) && ((pc0_x <= 24.0) || ( !((( !(pc0_l2 != 0)) && ((pc0_l0 != 0) && ( !(pc0_l1 != 0)))) && ((_x_pc0_l2 != 0) && ((_x_pc0_l0 != 0) && ( !(_x_pc0_l1 != 0)))))))) && ((( !(_x_pc0_l2 != 0)) && ((_x_pc0_l0 != 0) && (_x_pc0_l1 != 0))) || ( !((( !(pc0_l2 != 0)) && ((pc0_l0 != 0) && (pc0_l1 != 0))) && ((delta == 0.0) && ( !(( !(pc0_evt0 != 0)) && ( !(pc0_evt1 != 0))))))))) && ((( !(_x_pc0_l2 != 0)) && (( !(_x_pc0_l0 != 0)) && ( !(_x_pc0_l1 != 0)))) || ( !(((pc0_l2 != 0) && ((pc0_l0 != 0) && ( !(pc0_l1 != 0)))) && ((delta == 0.0) && ( !(( !(pc0_evt0 != 0)) && ( !(pc0_evt1 != 0))))))))) && ((((((( !(_x_a2_evt0 != 0)) && ( !(_x_a2_evt1 != 0))) || (((_x_a2_evt1 != 0) && ( !(_x_a2_evt0 != 0))) || ((_x_a2_evt0 != 0) && ( !(_x_a2_evt1 != 0))))) && (((a2_l != 0) == (_x_a2_l != 0)) || ( !(( !(delta <= 0.0)) || (( !(a2_evt0 != 0)) && ( !(a2_evt1 != 0))))))) && (((_x_id == 0) && ((((a2_evt1 != 0) && ( !(a2_evt0 != 0))) && (_x_a2_l != 0)) && (id == 3))) || ( !(( !(a2_l != 0)) && ((delta == 0.0) && ( !(( !(a2_evt0 != 0)) && ( !(a2_evt1 != 0))))))))) && (((((a2_evt0 != 0) && ( !(a2_evt1 != 0))) && ( !(_x_a2_l != 0))) && (_x_id == 3)) || ( !((a2_l != 0) && ((delta == 0.0) && ( !(( !(a2_evt0 != 0)) && ( !(a2_evt1 != 0))))))))) && ((((((( !(_x_a1_evt0 != 0)) && ( !(_x_a1_evt1 != 0))) || (((_x_a1_evt1 != 0) && ( !(_x_a1_evt0 != 0))) || ((_x_a1_evt0 != 0) && ( !(_x_a1_evt1 != 0))))) && (((a1_l != 0) == (_x_a1_l != 0)) || ( !(( !(delta <= 0.0)) || (( !(a1_evt0 != 0)) && ( !(a1_evt1 != 0))))))) && (((_x_id == 0) && ((((a1_evt1 != 0) && ( !(a1_evt0 != 0))) && (_x_a1_l != 0)) && (id == 2))) || ( !(( !(a1_l != 0)) && ((delta == 0.0) && ( !(( !(a1_evt0 != 0)) && ( !(a1_evt1 != 0))))))))) && (((((a1_evt0 != 0) && ( !(a1_evt1 != 0))) && ( !(_x_a1_l != 0))) && (_x_id == 2)) || ( !((a1_l != 0) && ((delta == 0.0) && ( !(( !(a1_evt0 != 0)) && ( !(a1_evt1 != 0))))))))) && ((((((( !(_x_a0_evt0 != 0)) && ( !(_x_a0_evt1 != 0))) || (((_x_a0_evt1 != 0) && ( !(_x_a0_evt0 != 0))) || ((_x_a0_evt0 != 0) && ( !(_x_a0_evt1 != 0))))) && (((a0_l != 0) == (_x_a0_l != 0)) || ( !(( !(delta <= 0.0)) || (( !(a0_evt0 != 0)) && ( !(a0_evt1 != 0))))))) && ((((((a0_evt1 != 0) && ( !(a0_evt0 != 0))) && (_x_a0_l != 0)) && (id == 1)) && (_x_id == 0)) || ( !(( !(a0_l != 0)) && ((delta == 0.0) && ( !(( !(a0_evt0 != 0)) && ( !(a0_evt1 != 0))))))))) && (((_x_id == 1) && (((a0_evt0 != 0) && ( !(a0_evt1 != 0))) && ( !(_x_a0_l != 0)))) || ( !((a0_l != 0) && ((delta == 0.0) && ( !(( !(a0_evt0 != 0)) && ( !(a0_evt1 != 0))))))))) && ((((((((c_initial != 0) == (_x_c_initial != 0)) || ( !(( !(c_move != 0)) || ( !(delta <= 0.0))))) && ((((id == 0) && (_x_id == 1)) && ( !(_x_c_initial != 0))) || ( !((delta == 0.0) && ((c_move != 0) && (c_initial != 0)))))) && (( !(_x_c_initial != 0)) || ( !(((c_move != 0) && (delta == 0.0)) && ( !(c_initial != 0)))))) && ((_x_id == 1) || ( !(((delta == 0.0) && (3 <= id)) && (( !(_x_c_initial != 0)) && ( !(c_initial != 0))))))) && ((_x_id == 1) || ( !((( !(_x_c_initial != 0)) && ( !(c_initial != 0))) && ((delta == 0.0) && ( !(3 <= id))))))) && (0.0 <= _x_delta)))))))) && ((_x_id == 2) || ((_x_id == 1) || (_x_id == 0)))) && ((id == _x_id) || ( !((( !(pc2_evt0 != 0)) && ( !(pc2_evt1 != 0))) && ((( !(pc1_evt0 != 0)) && ( !(pc1_evt1 != 0))) && ((( !(pc0_evt0 != 0)) && ( !(pc0_evt1 != 0))) && ((( !(a2_evt0 != 0)) && ( !(a2_evt1 != 0))) && ((( !(a1_evt0 != 0)) && ( !(a1_evt1 != 0))) && (( !(c_move != 0)) && (( !(a0_evt0 != 0)) && ( !(a0_evt1 != 0)))))))))))) && ((((a0_evt1 != 0) && ( !(a0_evt0 != 0))) == ((pc0_evt1 != 0) && ( !(pc0_evt0 != 0)))) || ( !(delta == 0.0)))) && (( !(delta == 0.0)) || (((a0_evt0 != 0) && ( !(a0_evt1 != 0))) == ((pc0_evt0 != 0) && ( !(pc0_evt1 != 0)))))) && (( !(delta == 0.0)) || (((a1_evt1 != 0) && ( !(a1_evt0 != 0))) == ((pc1_evt1 != 0) && ( !(pc1_evt0 != 0)))))) && (( !(delta == 0.0)) || (((a1_evt0 != 0) && ( !(a1_evt1 != 0))) == ((pc1_evt0 != 0) && ( !(pc1_evt1 != 0)))))) && (( !(delta == 0.0)) || (((a2_evt1 != 0) && ( !(a2_evt0 != 0))) == ((pc2_evt1 != 0) && ( !(pc2_evt0 != 0)))))) && (( !(delta == 0.0)) || (((a2_evt0 != 0) && ( !(a2_evt1 != 0))) == ((pc2_evt0 != 0) && ( !(pc2_evt1 != 0)))))) && (((delta == _x__diverge_delta) || ( !(1.0 <= _diverge_delta))) && ((1.0 <= _diverge_delta) || ((delta + (_diverge_delta + (-1.0 * _x__diverge_delta))) == 0.0))));
    pc2_l2 = _x_pc2_l2;
    pc2_l1 = _x_pc2_l1;
    a1_evt1 = _x_a1_evt1;
    a2_l = _x_a2_l;
    a1_evt0 = _x_a1_evt0;
    pc1_l0 = _x_pc1_l0;
    a0_evt1 = _x_a0_evt1;
    pc2_l0 = _x_pc2_l0;
    pc2_evt1 = _x_pc2_evt1;
    a0_evt0 = _x_a0_evt0;
    a1_l = _x_a1_l;
    delta = _x_delta;
    pc0_l2 = _x_pc0_l2;
    pc2_evt0 = _x_pc2_evt0;
    pc1_x = _x_pc1_x;
    pc0_x = _x_pc0_x;
    c_initial = _x_c_initial;
    pc0_evt0 = _x_pc0_evt0;
    pc0_evt1 = _x_pc0_evt1;
    pc0_l1 = _x_pc0_l1;
    a0_l = _x_a0_l;
    id = _x_id;
    pc1_evt0 = _x_pc1_evt0;
    c_move = _x_c_move;
    pc1_evt1 = _x_pc1_evt1;
    a2_evt0 = _x_a2_evt0;
    pc1_l1 = _x_pc1_l1;
    a2_evt1 = _x_a2_evt1;
    pc0_l0 = _x_pc0_l0;
    pc1_l2 = _x_pc1_l2;
    _diverge_delta = _x__diverge_delta;
    pc2_x = _x_pc2_x;

  }
}
