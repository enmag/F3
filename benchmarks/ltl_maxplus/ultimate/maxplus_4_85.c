//@ ltl invariant negative: (([] (x_1 - x_2 >= -20)) || (<> (x_0 - x_3 > 12)));

int main()
{
  float v0, _x_v0;
  float v1, _x_v1;
  float v2, _x_v2;
  float v3, _x_v3;
  while(1) {
_x_v0 = ((7.0 + v2) > (6.0 + v3)? (7.0 + v2) : (6.0 + v3));
_x_v1 = ((20.0 + v0) > (19.0 + v2)? (20.0 + v0) : (19.0 + v2));
_x_v2 = ((9.0 + v1) > (5.0 + v3)? (9.0 + v1) : (5.0 + v3));
_x_v3 = ((6.0 + v2) > (2.0 + v3)? (6.0 + v2) : (2.0 + v3));
v0 = _x_v0;
v1 = _x_v1;
v2 = _x_v2;
v3 = _x_v3;
  }
  return 0;
}
