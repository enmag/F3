//@ ltl invariant negative: ((X (x_3 - x_2 >= -7)) U (X (x_2 - x_3 > 14)));

int main()
{
  float v0, _x_v0;
  float v1, _x_v1;
  float v2, _x_v2;
  float v3, _x_v3;
  while(1) {
_x_v0 = ((6.0 + v1) > (10.0 + v2)? (6.0 + v1) : (10.0 + v2));
_x_v1 = ((15.0 + v1) > (1.0 + v3)? (15.0 + v1) : (1.0 + v3));
_x_v2 = ((16.0 + v1) > (7.0 + v3)? (16.0 + v1) : (7.0 + v3));
_x_v3 = ((7.0 + v0) > (15.0 + v2)? (7.0 + v0) : (15.0 + v2));
v0 = _x_v0;
v1 = _x_v1;
v2 = _x_v2;
v3 = _x_v3;
  }
  return 0;
}
