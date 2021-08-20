//@ ltl invariant negative: ((X (x_0 - x_2 >= -3)) || ([] (x_0 - x_1 > 8)));

int main()
{
  float v0, _x_v0;
  float v1, _x_v1;
  float v2, _x_v2;
  float v3, _x_v3;
  while(1) {
_x_v0 = ((2.0 + v0) > (4.0 + v1)? (2.0 + v0) : (4.0 + v1));
_x_v1 = ((12.0 + v1) > (4.0 + v2)? (12.0 + v1) : (4.0 + v2));
_x_v2 = ((9.0 + v2) > (1.0 + v3)? (9.0 + v2) : (1.0 + v3));
_x_v3 = ((15.0 + v0) > (15.0 + v2)? (15.0 + v0) : (15.0 + v2));
v0 = _x_v0;
v1 = _x_v1;
v2 = _x_v2;
v3 = _x_v3;
  }
  return 0;
}
