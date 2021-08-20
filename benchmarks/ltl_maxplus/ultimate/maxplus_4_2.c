//@ ltl invariant negative: (([] (x_3 - x_1 >= 9)) R (X (x_1 - x_2 >= -18)));

int main()
{
  float v0, _x_v0;
  float v1, _x_v1;
  float v2, _x_v2;
  float v3, _x_v3;
  while(1) {
_x_v0 = ((12.0 + v0) > (4.0 + v2)? (12.0 + v0) : (4.0 + v2));
_x_v1 = ((13.0 + v0) > (5.0 + v3)? (13.0 + v0) : (5.0 + v3));
_x_v2 = ((1.0 + v0) > (8.0 + v1)? (1.0 + v0) : (8.0 + v1));
_x_v3 = ((19.0 + v1) > (12.0 + v2)? (19.0 + v1) : (12.0 + v2));
v0 = _x_v0;
v1 = _x_v1;
v2 = _x_v2;
v3 = _x_v3;
  }
  return 0;
}
