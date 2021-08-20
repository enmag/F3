//@ ltl invariant negative: (X ((x_1 - x_3 > -10) && (X (x_1 - x_3 > 16))));

int main()
{
  float v0, _x_v0;
  float v1, _x_v1;
  float v2, _x_v2;
  float v3, _x_v3;
  while(1) {
_x_v0 = ((1.0 + v1) > (20.0 + v3)? (1.0 + v1) : (20.0 + v3));
_x_v1 = ((3.0 + v1) > (12.0 + v2)? (3.0 + v1) : (12.0 + v2));
_x_v2 = ((20.0 + v0) > (20.0 + v1)? (20.0 + v0) : (20.0 + v1));
_x_v3 = ((11.0 + v1) > (17.0 + v3)? (11.0 + v1) : (17.0 + v3));
v0 = _x_v0;
v1 = _x_v1;
v2 = _x_v2;
v3 = _x_v3;
  }
  return 0;
}
