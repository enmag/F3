//@ ltl invariant negative: ([] (([] (x_3 - x_2 > -5)) U (x_1 - x_2 >= -8)));

int main()
{
  float v0, _x_v0;
  float v1, _x_v1;
  float v2, _x_v2;
  float v3, _x_v3;
  while(1) {
_x_v0 = ((18.0 + v1) > (7.0 + v3)? (18.0 + v1) : (7.0 + v3));
_x_v1 = ((18.0 + v0) > (8.0 + v3)? (18.0 + v0) : (8.0 + v3));
_x_v2 = ((6.0 + v2) > (19.0 + v3)? (6.0 + v2) : (19.0 + v3));
_x_v3 = ((1.0 + v1) > (2.0 + v2)? (1.0 + v1) : (2.0 + v2));
v0 = _x_v0;
v1 = _x_v1;
v2 = _x_v2;
v3 = _x_v3;
  }
  return 0;
}
