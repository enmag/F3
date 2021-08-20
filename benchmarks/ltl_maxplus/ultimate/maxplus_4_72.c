//@ ltl invariant negative: (X ((x_1 - x_2 >= -13) R ([] (x_3 - x_2 > 11))));

int main()
{
  float v0, _x_v0;
  float v1, _x_v1;
  float v2, _x_v2;
  float v3, _x_v3;
  while(1) {
_x_v0 = ((17.0 + v1) > (3.0 + v2)? (17.0 + v1) : (3.0 + v2));
_x_v1 = ((15.0 + v0) > (12.0 + v1)? (15.0 + v0) : (12.0 + v1));
_x_v2 = ((20.0 + v2) > (7.0 + v3)? (20.0 + v2) : (7.0 + v3));
_x_v3 = ((15.0 + v0) > (10.0 + v3)? (15.0 + v0) : (10.0 + v3));
v0 = _x_v0;
v1 = _x_v1;
v2 = _x_v2;
v3 = _x_v3;
  }
  return 0;
}
