//@ ltl invariant negative: ( ( ([] (<> AP((id == 1)))) || (! ([] ( (! ( (! AP((pc0_l2 != 0))) && ( AP((pc0_l0 != 0)) && AP((pc0_l1 != 0))))) || (! ( (! AP((pc1_l2 != 0))) && ( AP((pc1_l0 != 0)) && AP((pc1_l1 != 0))))))))) || (! ([] (<> AP((1.0 <= _diverge_delta))))));

extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);

char __VERIFIER_nondet_bool(void) {
  return __VERIFIER_nondet_int() != 0;
}


char pc1_l2, _x_pc1_l2;
char pc0_l2, _x_pc0_l2;
char pc1_l1, _x_pc1_l1;
char pc0_l1, _x_pc0_l1;
char pc1_l0, _x_pc1_l0;
char pc0_l0, _x_pc0_l0;
float delta, _x_delta;
float _diverge_delta, _x__diverge_delta;
int id, _x_id;
char a1_l, _x_a1_l;
char c_move, _x_c_move;
char c_initial, _x_c_initial;
char a0_l, _x_a0_l;
char pc1_evt1, _x_pc1_evt1;
char pc0_evt1, _x_pc0_evt1;
char a0_evt0, _x_a0_evt0;
char a0_evt1, _x_a0_evt1;
char a1_evt0, _x_a1_evt0;
char a1_evt1, _x_a1_evt1;
float pc1_x, _x_pc1_x;
float pc0_x, _x_pc0_x;
char pc1_evt0, _x_pc1_evt0;
char pc0_evt0, _x_pc0_evt0;

int main()
{
  pc1_l2 = __VERIFIER_nondet_bool();
  pc0_l2 = __VERIFIER_nondet_bool();
  pc1_l1 = __VERIFIER_nondet_bool();
  pc0_l1 = __VERIFIER_nondet_bool();
  pc1_l0 = __VERIFIER_nondet_bool();
  pc0_l0 = __VERIFIER_nondet_bool();
  delta = __VERIFIER_nondet_float();
  _diverge_delta = __VERIFIER_nondet_float();
  id = __VERIFIER_nondet_int();
  a1_l = __VERIFIER_nondet_bool();
  c_move = __VERIFIER_nondet_bool();
  c_initial = __VERIFIER_nondet_bool();
  a0_l = __VERIFIER_nondet_bool();
  pc1_evt1 = __VERIFIER_nondet_bool();
  pc0_evt1 = __VERIFIER_nondet_bool();
  a0_evt0 = __VERIFIER_nondet_bool();
  a0_evt1 = __VERIFIER_nondet_bool();
  a1_evt0 = __VERIFIER_nondet_bool();
  a1_evt1 = __VERIFIER_nondet_bool();
  pc1_x = __VERIFIER_nondet_float();
  pc0_x = __VERIFIER_nondet_float();
  pc1_evt0 = __VERIFIER_nondet_bool();
  pc0_evt0 = __VERIFIER_nondet_bool();

  int __ok = (((((((( !(pc1_l2 != 0)) && (( !(pc1_l0 != 0)) && ( !(pc1_l1 != 0)))) && (pc1_x == 0.0)) && (((( !(pc1_evt0 != 0)) && ( !(pc1_evt1 != 0))) || ((pc1_evt1 != 0) && ( !(pc1_evt0 != 0)))) || (((pc1_evt0 != 0) && ( !(pc1_evt1 != 0))) || ((pc1_evt0 != 0) && (pc1_evt1 != 0))))) && ((( !(pc1_l2 != 0)) && ((pc1_l0 != 0) && (pc1_l1 != 0))) || ((((( !(pc1_l2 != 0)) && (( !(pc1_l0 != 0)) && ( !(pc1_l1 != 0)))) || ((pc1_l2 != 0) && (( !(pc1_l0 != 0)) && ( !(pc1_l1 != 0))))) || ((( !(pc1_l2 != 0)) && ((pc1_l1 != 0) && ( !(pc1_l0 != 0)))) || ((pc1_l2 != 0) && ((pc1_l1 != 0) && ( !(pc1_l0 != 0)))))) || ((( !(pc1_l2 != 0)) && ((pc1_l0 != 0) && ( !(pc1_l1 != 0)))) || ((pc1_l2 != 0) && ((pc1_l0 != 0) && ( !(pc1_l1 != 0)))))))) && (((((( !(pc0_l2 != 0)) && (( !(pc0_l0 != 0)) && ( !(pc0_l1 != 0)))) && (pc0_x == 0.0)) && (((( !(pc0_evt0 != 0)) && ( !(pc0_evt1 != 0))) || ((pc0_evt1 != 0) && ( !(pc0_evt0 != 0)))) || (((pc0_evt0 != 0) && ( !(pc0_evt1 != 0))) || ((pc0_evt0 != 0) && (pc0_evt1 != 0))))) && ((( !(pc0_l2 != 0)) && ((pc0_l0 != 0) && (pc0_l1 != 0))) || ((((( !(pc0_l2 != 0)) && (( !(pc0_l0 != 0)) && ( !(pc0_l1 != 0)))) || ((pc0_l2 != 0) && (( !(pc0_l0 != 0)) && ( !(pc0_l1 != 0))))) || ((( !(pc0_l2 != 0)) && ((pc0_l1 != 0) && ( !(pc0_l0 != 0)))) || ((pc0_l2 != 0) && ((pc0_l1 != 0) && ( !(pc0_l0 != 0)))))) || ((( !(pc0_l2 != 0)) && ((pc0_l0 != 0) && ( !(pc0_l1 != 0)))) || ((pc0_l2 != 0) && ((pc0_l0 != 0) && ( !(pc0_l1 != 0)))))))) && ((( !(a1_l != 0)) && ((( !(a1_evt0 != 0)) && ( !(a1_evt1 != 0))) || (((a1_evt1 != 0) && ( !(a1_evt0 != 0))) || ((a1_evt0 != 0) && ( !(a1_evt1 != 0)))))) && ((( !(a0_l != 0)) && ((( !(a0_evt0 != 0)) && ( !(a0_evt1 != 0))) || (((a0_evt1 != 0) && ( !(a0_evt0 != 0))) || ((a0_evt0 != 0) && ( !(a0_evt1 != 0)))))) && ((c_initial != 0) && (0.0 <= delta)))))) && ((id == 0) || (id == 1))) && (delta == _diverge_delta));
  while (__ok) {
    _x_pc1_l2 = __VERIFIER_nondet_bool();
    _x_pc0_l2 = __VERIFIER_nondet_bool();
    _x_pc1_l1 = __VERIFIER_nondet_bool();
    _x_pc0_l1 = __VERIFIER_nondet_bool();
    _x_pc1_l0 = __VERIFIER_nondet_bool();
    _x_pc0_l0 = __VERIFIER_nondet_bool();
    _x_delta = __VERIFIER_nondet_float();
    _x__diverge_delta = __VERIFIER_nondet_float();
    _x_id = __VERIFIER_nondet_int();
    _x_a1_l = __VERIFIER_nondet_bool();
    _x_c_move = __VERIFIER_nondet_bool();
    _x_c_initial = __VERIFIER_nondet_bool();
    _x_a0_l = __VERIFIER_nondet_bool();
    _x_pc1_evt1 = __VERIFIER_nondet_bool();
    _x_pc0_evt1 = __VERIFIER_nondet_bool();
    _x_a0_evt0 = __VERIFIER_nondet_bool();
    _x_a0_evt1 = __VERIFIER_nondet_bool();
    _x_a1_evt0 = __VERIFIER_nondet_bool();
    _x_a1_evt1 = __VERIFIER_nondet_bool();
    _x_pc1_x = __VERIFIER_nondet_float();
    _x_pc0_x = __VERIFIER_nondet_float();
    _x_pc1_evt0 = __VERIFIER_nondet_bool();
    _x_pc0_evt0 = __VERIFIER_nondet_bool();

    __ok = (((((((((((((((((((((((((((( !(_x_pc1_evt0 != 0)) && ( !(_x_pc1_evt1 != 0))) || ((_x_pc1_evt1 != 0) && ( !(_x_pc1_evt0 != 0)))) || (((_x_pc1_evt0 != 0) && ( !(_x_pc1_evt1 != 0))) || ((_x_pc1_evt0 != 0) && (_x_pc1_evt1 != 0)))) && ((( !(_x_pc1_l2 != 0)) && ((_x_pc1_l0 != 0) && (_x_pc1_l1 != 0))) || ((((( !(_x_pc1_l2 != 0)) && (( !(_x_pc1_l0 != 0)) && ( !(_x_pc1_l1 != 0)))) || ((_x_pc1_l2 != 0) && (( !(_x_pc1_l0 != 0)) && ( !(_x_pc1_l1 != 0))))) || ((( !(_x_pc1_l2 != 0)) && ((_x_pc1_l1 != 0) && ( !(_x_pc1_l0 != 0)))) || ((_x_pc1_l2 != 0) && ((_x_pc1_l1 != 0) && ( !(_x_pc1_l0 != 0)))))) || ((( !(_x_pc1_l2 != 0)) && ((_x_pc1_l0 != 0) && ( !(_x_pc1_l1 != 0)))) || ((_x_pc1_l2 != 0) && ((_x_pc1_l0 != 0) && ( !(_x_pc1_l1 != 0)))))))) && ((delta <= 0.0) || (((((pc1_l0 != 0) == (_x_pc1_l0 != 0)) && ((pc1_l1 != 0) == (_x_pc1_l1 != 0))) && ((pc1_l2 != 0) == (_x_pc1_l2 != 0))) && ((delta + (pc1_x + (-1.0 * _x_pc1_x))) == 0.0)))) && ((((((pc1_l0 != 0) == (_x_pc1_l0 != 0)) && ((pc1_l1 != 0) == (_x_pc1_l1 != 0))) && ((pc1_l2 != 0) == (_x_pc1_l2 != 0))) && ((delta + (pc1_x + (-1.0 * _x_pc1_x))) == 0.0)) || ( !(( !(pc1_evt0 != 0)) && ( !(pc1_evt1 != 0)))))) && (((((pc1_evt0 != 0) && (pc1_evt1 != 0)) && (pc1_x <= 50.0)) && (((_x_pc1_l2 != 0) && (( !(_x_pc1_l0 != 0)) && ( !(_x_pc1_l1 != 0)))) && (_x_pc1_x == 0.0))) || ( !((( !(pc1_l2 != 0)) && (( !(pc1_l0 != 0)) && ( !(pc1_l1 != 0)))) && ((delta == 0.0) && ( !(( !(pc1_evt0 != 0)) && ( !(pc1_evt1 != 0))))))))) && ((((pc1_evt0 != 0) && (pc1_evt1 != 0)) && ((( !(_x_pc1_l2 != 0)) && (( !(_x_pc1_l0 != 0)) && ( !(_x_pc1_l1 != 0)))) || (( !(_x_pc1_l2 != 0)) && ((_x_pc1_l1 != 0) && ( !(_x_pc1_l0 != 0)))))) || ( !(((pc1_l2 != 0) && (( !(pc1_l0 != 0)) && ( !(pc1_l1 != 0)))) && ((delta == 0.0) && ( !(( !(pc1_evt0 != 0)) && ( !(pc1_evt1 != 0))))))))) && (((_x_pc1_x == 0.0) && (25.0 <= pc1_x)) || ( !((( !(_x_pc1_l2 != 0)) && (( !(_x_pc1_l0 != 0)) && ( !(_x_pc1_l1 != 0)))) && ((pc1_l2 != 0) && (( !(pc1_l0 != 0)) && ( !(pc1_l1 != 0)))))))) && (((pc1_x <= 24.0) && (pc1_x == _x_pc1_x)) || ( !(((pc1_l2 != 0) && (( !(pc1_l0 != 0)) && ( !(pc1_l1 != 0)))) && (( !(_x_pc1_l2 != 0)) && ((_x_pc1_l1 != 0) && ( !(_x_pc1_l0 != 0)))))))) && (((_x_pc1_x == 0.0) && (((pc1_evt1 != 0) && ( !(pc1_evt0 != 0))) && ((_x_pc1_l2 != 0) && ((_x_pc1_l1 != 0) && ( !(_x_pc1_l0 != 0)))))) || ( !((( !(pc1_l2 != 0)) && ((pc1_l1 != 0) && ( !(pc1_l0 != 0)))) && ((delta == 0.0) && ( !(( !(pc1_evt0 != 0)) && ( !(pc1_evt1 != 0))))))))) && (((( !(_x_pc1_l2 != 0)) && ((_x_pc1_l0 != 0) && ( !(_x_pc1_l1 != 0)))) || (( !(_x_pc1_l2 != 0)) && ((_x_pc1_l0 != 0) && (_x_pc1_l1 != 0)))) || ( !(((pc1_l2 != 0) && ((pc1_l1 != 0) && ( !(pc1_l0 != 0)))) && ((delta == 0.0) && ( !(( !(pc1_evt0 != 0)) && ( !(pc1_evt1 != 0))))))))) && (((pc1_x == _x_pc1_x) && (((pc1_evt0 != 0) && (pc1_evt1 != 0)) && (50.0 <= pc1_x))) || ( !(((pc1_l2 != 0) && ((pc1_l1 != 0) && ( !(pc1_l0 != 0)))) && (( !(_x_pc1_l2 != 0)) && ((_x_pc1_l0 != 0) && (_x_pc1_l1 != 0))))))) && (((_x_pc1_x == 0.0) && (((pc1_evt0 != 0) && ( !(pc1_evt1 != 0))) && (pc1_x <= 25.0))) || ( !(((pc1_l2 != 0) && ((pc1_l1 != 0) && ( !(pc1_l0 != 0)))) && (( !(_x_pc1_l2 != 0)) && ((_x_pc1_l0 != 0) && ( !(_x_pc1_l1 != 0)))))))) && (((((pc1_evt0 != 0) && (pc1_evt1 != 0)) && (pc1_x == _x_pc1_x)) && (((_x_pc1_l2 != 0) && ((_x_pc1_l0 != 0) && ( !(_x_pc1_l1 != 0)))) || (( !(_x_pc1_l2 != 0)) && ((_x_pc1_l0 != 0) && (_x_pc1_l1 != 0))))) || ( !((( !(pc1_l2 != 0)) && ((pc1_l0 != 0) && ( !(pc1_l1 != 0)))) && ((delta == 0.0) && ( !(( !(pc1_evt0 != 0)) && ( !(pc1_evt1 != 0))))))))) && ((25.0 <= pc1_x) || ( !((( !(pc1_l2 != 0)) && ((pc1_l0 != 0) && ( !(pc1_l1 != 0)))) && (( !(_x_pc1_l2 != 0)) && ((_x_pc1_l0 != 0) && (_x_pc1_l1 != 0))))))) && ((pc1_x <= 24.0) || ( !((( !(pc1_l2 != 0)) && ((pc1_l0 != 0) && ( !(pc1_l1 != 0)))) && ((_x_pc1_l2 != 0) && ((_x_pc1_l0 != 0) && ( !(_x_pc1_l1 != 0)))))))) && ((( !(_x_pc1_l2 != 0)) && ((_x_pc1_l0 != 0) && (_x_pc1_l1 != 0))) || ( !((( !(pc1_l2 != 0)) && ((pc1_l0 != 0) && (pc1_l1 != 0))) && ((delta == 0.0) && ( !(( !(pc1_evt0 != 0)) && ( !(pc1_evt1 != 0))))))))) && ((( !(_x_pc1_l2 != 0)) && (( !(_x_pc1_l0 != 0)) && ( !(_x_pc1_l1 != 0)))) || ( !(((pc1_l2 != 0) && ((pc1_l0 != 0) && ( !(pc1_l1 != 0)))) && ((delta == 0.0) && ( !(( !(pc1_evt0 != 0)) && ( !(pc1_evt1 != 0))))))))) && ((((((((((((((((((((( !(_x_pc0_evt0 != 0)) && ( !(_x_pc0_evt1 != 0))) || ((_x_pc0_evt1 != 0) && ( !(_x_pc0_evt0 != 0)))) || (((_x_pc0_evt0 != 0) && ( !(_x_pc0_evt1 != 0))) || ((_x_pc0_evt0 != 0) && (_x_pc0_evt1 != 0)))) && ((( !(_x_pc0_l2 != 0)) && ((_x_pc0_l0 != 0) && (_x_pc0_l1 != 0))) || ((((( !(_x_pc0_l2 != 0)) && (( !(_x_pc0_l0 != 0)) && ( !(_x_pc0_l1 != 0)))) || ((_x_pc0_l2 != 0) && (( !(_x_pc0_l0 != 0)) && ( !(_x_pc0_l1 != 0))))) || ((( !(_x_pc0_l2 != 0)) && ((_x_pc0_l1 != 0) && ( !(_x_pc0_l0 != 0)))) || ((_x_pc0_l2 != 0) && ((_x_pc0_l1 != 0) && ( !(_x_pc0_l0 != 0)))))) || ((( !(_x_pc0_l2 != 0)) && ((_x_pc0_l0 != 0) && ( !(_x_pc0_l1 != 0)))) || ((_x_pc0_l2 != 0) && ((_x_pc0_l0 != 0) && ( !(_x_pc0_l1 != 0)))))))) && ((delta <= 0.0) || (((((pc0_l0 != 0) == (_x_pc0_l0 != 0)) && ((pc0_l1 != 0) == (_x_pc0_l1 != 0))) && ((pc0_l2 != 0) == (_x_pc0_l2 != 0))) && ((delta + (pc0_x + (-1.0 * _x_pc0_x))) == 0.0)))) && ((((((pc0_l0 != 0) == (_x_pc0_l0 != 0)) && ((pc0_l1 != 0) == (_x_pc0_l1 != 0))) && ((pc0_l2 != 0) == (_x_pc0_l2 != 0))) && ((delta + (pc0_x + (-1.0 * _x_pc0_x))) == 0.0)) || ( !(( !(pc0_evt0 != 0)) && ( !(pc0_evt1 != 0)))))) && (((((pc0_evt0 != 0) && (pc0_evt1 != 0)) && (pc0_x <= 50.0)) && (((_x_pc0_l2 != 0) && (( !(_x_pc0_l0 != 0)) && ( !(_x_pc0_l1 != 0)))) && (_x_pc0_x == 0.0))) || ( !((( !(pc0_l2 != 0)) && (( !(pc0_l0 != 0)) && ( !(pc0_l1 != 0)))) && ((delta == 0.0) && ( !(( !(pc0_evt0 != 0)) && ( !(pc0_evt1 != 0))))))))) && ((((pc0_evt0 != 0) && (pc0_evt1 != 0)) && ((( !(_x_pc0_l2 != 0)) && (( !(_x_pc0_l0 != 0)) && ( !(_x_pc0_l1 != 0)))) || (( !(_x_pc0_l2 != 0)) && ((_x_pc0_l1 != 0) && ( !(_x_pc0_l0 != 0)))))) || ( !(((pc0_l2 != 0) && (( !(pc0_l0 != 0)) && ( !(pc0_l1 != 0)))) && ((delta == 0.0) && ( !(( !(pc0_evt0 != 0)) && ( !(pc0_evt1 != 0))))))))) && (((_x_pc0_x == 0.0) && (25.0 <= pc0_x)) || ( !((( !(_x_pc0_l2 != 0)) && (( !(_x_pc0_l0 != 0)) && ( !(_x_pc0_l1 != 0)))) && ((pc0_l2 != 0) && (( !(pc0_l0 != 0)) && ( !(pc0_l1 != 0)))))))) && (((pc0_x <= 24.0) && (pc0_x == _x_pc0_x)) || ( !(((pc0_l2 != 0) && (( !(pc0_l0 != 0)) && ( !(pc0_l1 != 0)))) && (( !(_x_pc0_l2 != 0)) && ((_x_pc0_l1 != 0) && ( !(_x_pc0_l0 != 0)))))))) && (((_x_pc0_x == 0.0) && (((pc0_evt1 != 0) && ( !(pc0_evt0 != 0))) && ((_x_pc0_l2 != 0) && ((_x_pc0_l1 != 0) && ( !(_x_pc0_l0 != 0)))))) || ( !((( !(pc0_l2 != 0)) && ((pc0_l1 != 0) && ( !(pc0_l0 != 0)))) && ((delta == 0.0) && ( !(( !(pc0_evt0 != 0)) && ( !(pc0_evt1 != 0))))))))) && (((( !(_x_pc0_l2 != 0)) && ((_x_pc0_l0 != 0) && ( !(_x_pc0_l1 != 0)))) || (( !(_x_pc0_l2 != 0)) && ((_x_pc0_l0 != 0) && (_x_pc0_l1 != 0)))) || ( !(((pc0_l2 != 0) && ((pc0_l1 != 0) && ( !(pc0_l0 != 0)))) && ((delta == 0.0) && ( !(( !(pc0_evt0 != 0)) && ( !(pc0_evt1 != 0))))))))) && (((pc0_x == _x_pc0_x) && (((pc0_evt0 != 0) && (pc0_evt1 != 0)) && (50.0 <= pc0_x))) || ( !(((pc0_l2 != 0) && ((pc0_l1 != 0) && ( !(pc0_l0 != 0)))) && (( !(_x_pc0_l2 != 0)) && ((_x_pc0_l0 != 0) && (_x_pc0_l1 != 0))))))) && (((_x_pc0_x == 0.0) && (((pc0_evt0 != 0) && ( !(pc0_evt1 != 0))) && (pc0_x <= 25.0))) || ( !(((pc0_l2 != 0) && ((pc0_l1 != 0) && ( !(pc0_l0 != 0)))) && (( !(_x_pc0_l2 != 0)) && ((_x_pc0_l0 != 0) && ( !(_x_pc0_l1 != 0)))))))) && (((((pc0_evt0 != 0) && (pc0_evt1 != 0)) && (pc0_x == _x_pc0_x)) && (((_x_pc0_l2 != 0) && ((_x_pc0_l0 != 0) && ( !(_x_pc0_l1 != 0)))) || (( !(_x_pc0_l2 != 0)) && ((_x_pc0_l0 != 0) && (_x_pc0_l1 != 0))))) || ( !((( !(pc0_l2 != 0)) && ((pc0_l0 != 0) && ( !(pc0_l1 != 0)))) && ((delta == 0.0) && ( !(( !(pc0_evt0 != 0)) && ( !(pc0_evt1 != 0))))))))) && ((25.0 <= pc0_x) || ( !((( !(pc0_l2 != 0)) && ((pc0_l0 != 0) && ( !(pc0_l1 != 0)))) && (( !(_x_pc0_l2 != 0)) && ((_x_pc0_l0 != 0) && (_x_pc0_l1 != 0))))))) && ((pc0_x <= 24.0) || ( !((( !(pc0_l2 != 0)) && ((pc0_l0 != 0) && ( !(pc0_l1 != 0)))) && ((_x_pc0_l2 != 0) && ((_x_pc0_l0 != 0) && ( !(_x_pc0_l1 != 0)))))))) && ((( !(_x_pc0_l2 != 0)) && ((_x_pc0_l0 != 0) && (_x_pc0_l1 != 0))) || ( !((( !(pc0_l2 != 0)) && ((pc0_l0 != 0) && (pc0_l1 != 0))) && ((delta == 0.0) && ( !(( !(pc0_evt0 != 0)) && ( !(pc0_evt1 != 0))))))))) && ((( !(_x_pc0_l2 != 0)) && (( !(_x_pc0_l0 != 0)) && ( !(_x_pc0_l1 != 0)))) || ( !(((pc0_l2 != 0) && ((pc0_l0 != 0) && ( !(pc0_l1 != 0)))) && ((delta == 0.0) && ( !(( !(pc0_evt0 != 0)) && ( !(pc0_evt1 != 0))))))))) && ((((((( !(_x_a1_evt0 != 0)) && ( !(_x_a1_evt1 != 0))) || (((_x_a1_evt1 != 0) && ( !(_x_a1_evt0 != 0))) || ((_x_a1_evt0 != 0) && ( !(_x_a1_evt1 != 0))))) && (((a1_l != 0) == (_x_a1_l != 0)) || ( !(( !(delta <= 0.0)) || (( !(a1_evt0 != 0)) && ( !(a1_evt1 != 0))))))) && (((_x_id == 0) && ((((a1_evt1 != 0) && ( !(a1_evt0 != 0))) && (_x_a1_l != 0)) && (id == 2))) || ( !(( !(a1_l != 0)) && ((delta == 0.0) && ( !(( !(a1_evt0 != 0)) && ( !(a1_evt1 != 0))))))))) && (((((a1_evt0 != 0) && ( !(a1_evt1 != 0))) && ( !(_x_a1_l != 0))) && (_x_id == 2)) || ( !((a1_l != 0) && ((delta == 0.0) && ( !(( !(a1_evt0 != 0)) && ( !(a1_evt1 != 0))))))))) && ((((((( !(_x_a0_evt0 != 0)) && ( !(_x_a0_evt1 != 0))) || (((_x_a0_evt1 != 0) && ( !(_x_a0_evt0 != 0))) || ((_x_a0_evt0 != 0) && ( !(_x_a0_evt1 != 0))))) && (((a0_l != 0) == (_x_a0_l != 0)) || ( !(( !(delta <= 0.0)) || (( !(a0_evt0 != 0)) && ( !(a0_evt1 != 0))))))) && ((((((a0_evt1 != 0) && ( !(a0_evt0 != 0))) && (_x_a0_l != 0)) && (id == 1)) && (_x_id == 0)) || ( !(( !(a0_l != 0)) && ((delta == 0.0) && ( !(( !(a0_evt0 != 0)) && ( !(a0_evt1 != 0))))))))) && (((_x_id == 1) && (((a0_evt0 != 0) && ( !(a0_evt1 != 0))) && ( !(_x_a0_l != 0)))) || ( !((a0_l != 0) && ((delta == 0.0) && ( !(( !(a0_evt0 != 0)) && ( !(a0_evt1 != 0))))))))) && ((((((((c_initial != 0) == (_x_c_initial != 0)) || ( !(( !(c_move != 0)) || ( !(delta <= 0.0))))) && ((((id == 0) && (_x_id == 1)) && ( !(_x_c_initial != 0))) || ( !((delta == 0.0) && ((c_move != 0) && (c_initial != 0)))))) && (( !(_x_c_initial != 0)) || ( !(((c_move != 0) && (delta == 0.0)) && ( !(c_initial != 0)))))) && ((_x_id == 1) || ( !(((delta == 0.0) && (2 <= id)) && (( !(_x_c_initial != 0)) && ( !(c_initial != 0))))))) && ((_x_id == 1) || ( !((( !(_x_c_initial != 0)) && ( !(c_initial != 0))) && ((delta == 0.0) && ( !(2 <= id))))))) && (0.0 <= _x_delta)))))) && ((_x_id == 1) || (_x_id == 0))) && ((id == _x_id) || ( !((( !(pc1_evt0 != 0)) && ( !(pc1_evt1 != 0))) && ((( !(pc0_evt0 != 0)) && ( !(pc0_evt1 != 0))) && ((( !(a1_evt0 != 0)) && ( !(a1_evt1 != 0))) && (( !(c_move != 0)) && (( !(a0_evt0 != 0)) && ( !(a0_evt1 != 0)))))))))) && ((((a0_evt1 != 0) && ( !(a0_evt0 != 0))) == ((pc0_evt1 != 0) && ( !(pc0_evt0 != 0)))) || ( !(delta == 0.0)))) && (( !(delta == 0.0)) || (((a0_evt0 != 0) && ( !(a0_evt1 != 0))) == ((pc0_evt0 != 0) && ( !(pc0_evt1 != 0)))))) && (( !(delta == 0.0)) || (((a1_evt1 != 0) && ( !(a1_evt0 != 0))) == ((pc1_evt1 != 0) && ( !(pc1_evt0 != 0)))))) && (( !(delta == 0.0)) || (((a1_evt0 != 0) && ( !(a1_evt1 != 0))) == ((pc1_evt0 != 0) && ( !(pc1_evt1 != 0)))))) && (((delta == _x__diverge_delta) || ( !(1.0 <= _diverge_delta))) && ((1.0 <= _diverge_delta) || ((delta + (_diverge_delta + (-1.0 * _x__diverge_delta))) == 0.0))));
    pc1_l2 = _x_pc1_l2;
    pc0_l2 = _x_pc0_l2;
    pc1_l1 = _x_pc1_l1;
    pc0_l1 = _x_pc0_l1;
    pc1_l0 = _x_pc1_l0;
    pc0_l0 = _x_pc0_l0;
    delta = _x_delta;
    _diverge_delta = _x__diverge_delta;
    id = _x_id;
    a1_l = _x_a1_l;
    c_move = _x_c_move;
    c_initial = _x_c_initial;
    a0_l = _x_a0_l;
    pc1_evt1 = _x_pc1_evt1;
    pc0_evt1 = _x_pc0_evt1;
    a0_evt0 = _x_a0_evt0;
    a0_evt1 = _x_a0_evt1;
    a1_evt0 = _x_a1_evt0;
    a1_evt1 = _x_a1_evt1;
    pc1_x = _x_pc1_x;
    pc0_x = _x_pc0_x;
    pc1_evt0 = _x_pc1_evt0;
    pc0_evt0 = _x_pc0_evt0;

  }
}
