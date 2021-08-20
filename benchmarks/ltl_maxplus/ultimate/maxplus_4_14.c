//@ ltl invariant negative: (X (([] (x_1 - x_0 >= 6)) U (x_0 - x_3 >= 15)));

int main()
{
  float v0, _x_v0;
  float v1, _x_v1;
  float v2, _x_v2;
  float v3, _x_v3;
  while(1) {
_x_v0 = ((19.0 + v0) > (15.0 + v1)? (19.0 + v0) : (15.0 + v1));
_x_v1 = ((5.0 + v1) > (4.0 + v2)? (5.0 + v1) : (4.0 + v2));
_x_v2 = ((19.0 + v2) > (1.0 + v3)? (19.0 + v2) : (1.0 + v3));
_x_v3 = ((20.0 + v0) > (7.0 + v2)? (20.0 + v0) : (7.0 + v2));
v0 = _x_v0;
v1 = _x_v1;
v2 = _x_v2;
v3 = _x_v3;
  }
  return 0;
}
