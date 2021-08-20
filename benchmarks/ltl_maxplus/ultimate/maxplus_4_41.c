//@ ltl invariant negative: ((x_0 - x_2 > 0) U ((x_2 - x_0 > -10) U (x_1 - x_2 >= -6)));

int main()
{
  float v0, _x_v0;
  float v1, _x_v1;
  float v2, _x_v2;
  float v3, _x_v3;
  while(1) {
_x_v0 = ((12.0 + v1) > (18.0 + v2)? (12.0 + v1) : (18.0 + v2));
_x_v1 = ((20.0 + v0) > (4.0 + v1)? (20.0 + v0) : (4.0 + v1));
_x_v2 = ((20.0 + v0) > (19.0 + v3)? (20.0 + v0) : (19.0 + v3));
_x_v3 = ((5.0 + v0) > (13.0 + v3)? (5.0 + v0) : (13.0 + v3));
v0 = _x_v0;
v1 = _x_v1;
v2 = _x_v2;
v3 = _x_v3;
  }
  return 0;
}
