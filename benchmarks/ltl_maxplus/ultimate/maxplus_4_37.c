//@ ltl invariant negative: ((x_3 - x_1 > 3) || ((x_0 - x_1 >= -15) && (x_0 - x_1 > 8)));

int main()
{
  float v0, _x_v0;
  float v1, _x_v1;
  float v2, _x_v2;
  float v3, _x_v3;
  while(1) {
_x_v0 = ((9.0 + v1) > (7.0 + v3)? (9.0 + v1) : (7.0 + v3));
_x_v1 = ((2.0 + v0) > (5.0 + v3)? (2.0 + v0) : (5.0 + v3));
_x_v2 = ((9.0 + v1) > (17.0 + v3)? (9.0 + v1) : (17.0 + v3));
_x_v3 = ((7.0 + v1) > (16.0 + v2)? (7.0 + v1) : (16.0 + v2));
v0 = _x_v0;
v1 = _x_v1;
v2 = _x_v2;
v3 = _x_v3;
  }
  return 0;
}
