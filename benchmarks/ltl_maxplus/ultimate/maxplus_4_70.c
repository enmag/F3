//@ ltl invariant negative: ([] ((x_0 - x_3 > 5) R (X (x_3 - x_1 >= 7))));

int main()
{
  float v0, _x_v0;
  float v1, _x_v1;
  float v2, _x_v2;
  float v3, _x_v3;
  while(1) {
_x_v0 = ((9.0 + v2) > (4.0 + v3)? (9.0 + v2) : (4.0 + v3));
_x_v1 = ((2.0 + v2) > (15.0 + v3)? (2.0 + v2) : (15.0 + v3));
_x_v2 = ((6.0 + v0) > (11.0 + v1)? (6.0 + v0) : (11.0 + v1));
_x_v3 = ((7.0 + v1) > (4.0 + v3)? (7.0 + v1) : (4.0 + v3));
v0 = _x_v0;
v1 = _x_v1;
v2 = _x_v2;
v3 = _x_v3;
  }
  return 0;
}
