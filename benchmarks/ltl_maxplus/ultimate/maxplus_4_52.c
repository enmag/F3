//@ ltl invariant negative: ((x_0 - x_2 > 0) R ([] (<> (x_1 - x_0 >= -5))));

int main()
{
  float v0, _x_v0;
  float v1, _x_v1;
  float v2, _x_v2;
  float v3, _x_v3;
  while(1) {
_x_v0 = ((18.0 + v0) > (6.0 + v1)? (18.0 + v0) : (6.0 + v1));
_x_v1 = ((7.0 + v0) > (15.0 + v2)? (7.0 + v0) : (15.0 + v2));
_x_v2 = ((8.0 + v2) > (5.0 + v3)? (8.0 + v2) : (5.0 + v3));
_x_v3 = ((13.0 + v0) > (14.0 + v2)? (13.0 + v0) : (14.0 + v2));
v0 = _x_v0;
v1 = _x_v1;
v2 = _x_v2;
v3 = _x_v3;
  }
  return 0;
}
