//@ ltl invariant negative: ([] (([] (x_2 - x_0 > -19)) U (x_2 - x_3 >= 16)));

int main()
{
  float v0, _x_v0;
  float v1, _x_v1;
  float v2, _x_v2;
  float v3, _x_v3;
  while(1) {
_x_v0 = ((3.0 + v1) > (1.0 + v2)? (3.0 + v1) : (1.0 + v2));
_x_v1 = ((18.0 + v2) > (9.0 + v3)? (18.0 + v2) : (9.0 + v3));
_x_v2 = ((16.0 + v0) > (4.0 + v3)? (16.0 + v0) : (4.0 + v3));
_x_v3 = ((11.0 + v0) > (20.0 + v1)? (11.0 + v0) : (20.0 + v1));
v0 = _x_v0;
v1 = _x_v1;
v2 = _x_v2;
v3 = _x_v3;
  }
  return 0;
}
