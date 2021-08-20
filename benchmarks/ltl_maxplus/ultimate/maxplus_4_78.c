//@ ltl invariant negative: (X ((<> (x_0 - x_3 > -10)) R (x_3 - x_2 >= -11)));

int main()
{
  float v0, _x_v0;
  float v1, _x_v1;
  float v2, _x_v2;
  float v3, _x_v3;
  while(1) {
_x_v0 = ((10.0 + v0) > (7.0 + v2)? (10.0 + v0) : (7.0 + v2));
_x_v1 = ((8.0 + v0) > (3.0 + v3)? (8.0 + v0) : (3.0 + v3));
_x_v2 = ((3.0 + v1) > (5.0 + v3)? (3.0 + v1) : (5.0 + v3));
_x_v3 = ((6.0 + v1) > (12.0 + v2)? (6.0 + v1) : (12.0 + v2));
v0 = _x_v0;
v1 = _x_v1;
v2 = _x_v2;
v3 = _x_v3;
  }
  return 0;
}
