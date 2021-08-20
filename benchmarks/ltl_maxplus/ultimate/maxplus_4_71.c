//@ ltl invariant negative: ((x_2 - x_1 > -8) && ([] (<> (x_3 - x_0 > 19))));

int main()
{
  float v0, _x_v0;
  float v1, _x_v1;
  float v2, _x_v2;
  float v3, _x_v3;
  while(1) {
_x_v0 = ((1.0 + v1) > (20.0 + v3)? (1.0 + v1) : (20.0 + v3));
_x_v1 = ((7.0 + v0) > (6.0 + v2)? (7.0 + v0) : (6.0 + v2));
_x_v2 = ((9.0 + v0) > (15.0 + v1)? (9.0 + v0) : (15.0 + v1));
_x_v3 = ((5.0 + v1) > (1.0 + v3)? (5.0 + v1) : (1.0 + v3));
v0 = _x_v0;
v1 = _x_v1;
v2 = _x_v2;
v3 = _x_v3;
  }
  return 0;
}
