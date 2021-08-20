//@ ltl invariant negative: ((X (x_0 - x_3 > -18)) || (X (x_0 - x_2 > 13)));

int main()
{
  float v0, _x_v0;
  float v1, _x_v1;
  float v2, _x_v2;
  float v3, _x_v3;
  while(1) {
_x_v0 = ((13.0 + v1) > (9.0 + v3)? (13.0 + v1) : (9.0 + v3));
_x_v1 = ((1.0 + v1) > (1.0 + v2)? (1.0 + v1) : (1.0 + v2));
_x_v2 = ((5.0 + v0) > (16.0 + v2)? (5.0 + v0) : (16.0 + v2));
_x_v3 = ((6.0 + v1) > (14.0 + v2)? (6.0 + v1) : (14.0 + v2));
v0 = _x_v0;
v1 = _x_v1;
v2 = _x_v2;
v3 = _x_v3;
  }
  return 0;
}
