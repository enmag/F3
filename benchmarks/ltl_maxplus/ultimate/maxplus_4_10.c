//@ ltl invariant negative: (X (X ((x_0 - x_1 >= 6) R (x_1 - x_2 >= 12))));

int main()
{
  float v0, _x_v0;
  float v1, _x_v1;
  float v2, _x_v2;
  float v3, _x_v3;
  while(1) {
_x_v0 = ((2.0 + v0) > (1.0 + v1)? (2.0 + v0) : (1.0 + v1));
_x_v1 = ((7.0 + v1) > (12.0 + v2)? (7.0 + v1) : (12.0 + v2));
_x_v2 = ((5.0 + v0) > (3.0 + v3)? (5.0 + v0) : (3.0 + v3));
_x_v3 = ((7.0 + v2) > (17.0 + v3)? (7.0 + v2) : (17.0 + v3));
v0 = _x_v0;
v1 = _x_v1;
v2 = _x_v2;
v3 = _x_v3;
  }
  return 0;
}
