//@ ltl invariant negative: ((<> (x_0 - x_3 > 5)) && (X (x_2 - x_1 > -20)));

int main()
{
  float v0, _x_v0;
  float v1, _x_v1;
  float v2, _x_v2;
  float v3, _x_v3;
  while(1) {
_x_v0 = ((6.0 + v2) > (9.0 + v3)? (6.0 + v2) : (9.0 + v3));
_x_v1 = ((12.0 + v1) > (7.0 + v2)? (12.0 + v1) : (7.0 + v2));
_x_v2 = ((16.0 + v1) > (20.0 + v3)? (16.0 + v1) : (20.0 + v3));
_x_v3 = ((7.0 + v0) > (14.0 + v1)? (7.0 + v0) : (14.0 + v1));
v0 = _x_v0;
v1 = _x_v1;
v2 = _x_v2;
v3 = _x_v3;
  }
  return 0;
}
