//@ ltl invariant negative: ((X (x_3 - x_2 > 0)) || (<> (x_0 - x_2 > 11)));

int main()
{
  float v0, _x_v0;
  float v1, _x_v1;
  float v2, _x_v2;
  float v3, _x_v3;
  while(1) {
_x_v0 = ((10.0 + v1) > (3.0 + v2)? (10.0 + v1) : (3.0 + v2));
_x_v1 = ((8.0 + v0) > (8.0 + v3)? (8.0 + v0) : (8.0 + v3));
_x_v2 = ((12.0 + v1) > (1.0 + v3)? (12.0 + v1) : (1.0 + v3));
_x_v3 = ((18.0 + v0) > (7.0 + v3)? (18.0 + v0) : (7.0 + v3));
v0 = _x_v0;
v1 = _x_v1;
v2 = _x_v2;
v3 = _x_v3;
  }
  return 0;
}
