//@ ltl invariant negative: (X ((x_0 - x_3 > -3) || (X (x_2 - x_0 > 13))));

int main()
{
  float v0, _x_v0;
  float v1, _x_v1;
  float v2, _x_v2;
  float v3, _x_v3;
  while(1) {
_x_v0 = ((8.0 + v1) > (14.0 + v2)? (8.0 + v1) : (14.0 + v2));
_x_v1 = ((8.0 + v0) > (9.0 + v3)? (8.0 + v0) : (9.0 + v3));
_x_v2 = ((20.0 + v1) > (13.0 + v2)? (20.0 + v1) : (13.0 + v2));
_x_v3 = ((20.0 + v0) > (11.0 + v2)? (20.0 + v0) : (11.0 + v2));
v0 = _x_v0;
v1 = _x_v1;
v2 = _x_v2;
v3 = _x_v3;
  }
  return 0;
}
