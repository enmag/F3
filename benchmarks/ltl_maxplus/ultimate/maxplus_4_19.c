//@ ltl invariant negative: (((x_1 - x_3 >= -12) R (x_1 - x_2 > 13)) R (x_0 - x_2 >= -14));

int main()
{
  float v0, _x_v0;
  float v1, _x_v1;
  float v2, _x_v2;
  float v3, _x_v3;
  while(1) {
_x_v0 = ((17.0 + v1) > (6.0 + v2)? (17.0 + v1) : (6.0 + v2));
_x_v1 = ((16.0 + v1) > (19.0 + v3)? (16.0 + v1) : (19.0 + v3));
_x_v2 = ((4.0 + v1) > (17.0 + v2)? (4.0 + v1) : (17.0 + v2));
_x_v3 = ((9.0 + v0) > (5.0 + v3)? (9.0 + v0) : (5.0 + v3));
v0 = _x_v0;
v1 = _x_v1;
v2 = _x_v2;
v3 = _x_v3;
  }
  return 0;
}
