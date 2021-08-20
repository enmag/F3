//@ ltl invariant negative: ([] (X ((x_2 - x_0 > -6) R (x_0 - x_1 > -19))));

int main()
{
  float v0, _x_v0;
  float v1, _x_v1;
  float v2, _x_v2;
  float v3, _x_v3;
  while(1) {
_x_v0 = ((20.0 + v2) > (11.0 + v3)? (20.0 + v2) : (11.0 + v3));
_x_v1 = ((20.0 + v0) > (17.0 + v1)? (20.0 + v0) : (17.0 + v1));
_x_v2 = ((1.0 + v0) > (12.0 + v1)? (1.0 + v0) : (12.0 + v1));
_x_v3 = ((10.0 + v1) > (5.0 + v2)? (10.0 + v1) : (5.0 + v2));
v0 = _x_v0;
v1 = _x_v1;
v2 = _x_v2;
v3 = _x_v3;
  }
  return 0;
}
