//@ ltl invariant negative: (((x_3 - x_1 > 11) R (x_1 - x_3 >= 18)) R (x_3 - x_1 > 11));

int main()
{
  float v0, _x_v0;
  float v1, _x_v1;
  float v2, _x_v2;
  float v3, _x_v3;
  while(1) {
_x_v0 = ((20.0 + v2) > (18.0 + v3)? (20.0 + v2) : (18.0 + v3));
_x_v1 = ((4.0 + v2) > (11.0 + v3)? (4.0 + v2) : (11.0 + v3));
_x_v2 = ((5.0 + v0) > (15.0 + v3)? (5.0 + v0) : (15.0 + v3));
_x_v3 = ((16.0 + v0) > (13.0 + v1)? (16.0 + v0) : (13.0 + v1));
v0 = _x_v0;
v1 = _x_v1;
v2 = _x_v2;
v3 = _x_v3;
  }
  return 0;
}
