//@ ltl invariant negative: ((x_0 - x_1 >= -3) R (X ([] (x_1 - x_0 >= -12))));

int main()
{
  float v0, _x_v0;
  float v1, _x_v1;
  float v2, _x_v2;
  float v3, _x_v3;
  while(1) {
_x_v0 = ((16.0 + v2) > (14.0 + v3)? (16.0 + v2) : (14.0 + v3));
_x_v1 = ((8.0 + v1) > (20.0 + v2)? (8.0 + v1) : (20.0 + v2));
_x_v2 = ((16.0 + v0) > (18.0 + v1)? (16.0 + v0) : (18.0 + v1));
_x_v3 = ((6.0 + v2) > (19.0 + v3)? (6.0 + v2) : (19.0 + v3));
v0 = _x_v0;
v1 = _x_v1;
v2 = _x_v2;
v3 = _x_v3;
  }
  return 0;
}
