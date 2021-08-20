//@ ltl invariant negative: ((x_0 - x_3 > 17) R (X (X (x_3 - x_1 > -16))));

int main()
{
  float v0, _x_v0;
  float v1, _x_v1;
  float v2, _x_v2;
  float v3, _x_v3;
  while(1) {
_x_v0 = ((20.0 + v1) > (14.0 + v2)? (20.0 + v1) : (14.0 + v2));
_x_v1 = ((8.0 + v0) > (11.0 + v1)? (8.0 + v0) : (11.0 + v1));
_x_v2 = ((14.0 + v1) > (2.0 + v3)? (14.0 + v1) : (2.0 + v3));
_x_v3 = ((2.0 + v1) > (9.0 + v2)? (2.0 + v1) : (9.0 + v2));
v0 = _x_v0;
v1 = _x_v1;
v2 = _x_v2;
v3 = _x_v3;
  }
  return 0;
}
