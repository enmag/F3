//@ ltl invariant negative: (<> ([] ((x_3 - x_2 >= -10) && (x_3 - x_0 >= -1))));

int main()
{
  float v0, _x_v0;
  float v1, _x_v1;
  float v2, _x_v2;
  float v3, _x_v3;
  while(1) {
_x_v0 = ((5.0 + v0) > (6.0 + v1)? (5.0 + v0) : (6.0 + v1));
_x_v1 = ((15.0 + v0) > (7.0 + v3)? (15.0 + v0) : (7.0 + v3));
_x_v2 = ((1.0 + v1) > (10.0 + v3)? (1.0 + v1) : (10.0 + v3));
_x_v3 = ((5.0 + v2) > (9.0 + v3)? (5.0 + v2) : (9.0 + v3));
v0 = _x_v0;
v1 = _x_v1;
v2 = _x_v2;
v3 = _x_v3;
  }
  return 0;
}
