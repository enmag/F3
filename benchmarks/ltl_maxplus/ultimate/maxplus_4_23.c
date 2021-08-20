//@ ltl invariant negative: (([] (x_0 - x_2 >= -12)) U ([] (x_3 - x_2 > -13)));

int main()
{
  float v0, _x_v0;
  float v1, _x_v1;
  float v2, _x_v2;
  float v3, _x_v3;
  while(1) {
_x_v0 = ((11.0 + v1) > (5.0 + v2)? (11.0 + v1) : (5.0 + v2));
_x_v1 = ((18.0 + v0) > (5.0 + v2)? (18.0 + v0) : (5.0 + v2));
_x_v2 = ((6.0 + v2) > (10.0 + v3)? (6.0 + v2) : (10.0 + v3));
_x_v3 = ((8.0 + v0) > (3.0 + v3)? (8.0 + v0) : (3.0 + v3));
v0 = _x_v0;
v1 = _x_v1;
v2 = _x_v2;
v3 = _x_v3;
  }
  return 0;
}
