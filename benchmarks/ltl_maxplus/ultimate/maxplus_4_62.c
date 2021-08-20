//@ ltl invariant negative: ((X (X (x_2 - x_0 > -16))) U (x_1 - x_0 > 15));

int main()
{
  float v0, _x_v0;
  float v1, _x_v1;
  float v2, _x_v2;
  float v3, _x_v3;
  while(1) {
_x_v0 = ((14.0 + v1) > (17.0 + v2)? (14.0 + v1) : (17.0 + v2));
_x_v1 = ((8.0 + v0) > (17.0 + v1)? (8.0 + v0) : (17.0 + v1));
_x_v2 = ((11.0 + v0) > (15.0 + v3)? (11.0 + v0) : (15.0 + v3));
_x_v3 = ((18.0 + v0) > (4.0 + v1)? (18.0 + v0) : (4.0 + v1));
v0 = _x_v0;
v1 = _x_v1;
v2 = _x_v2;
v3 = _x_v3;
  }
  return 0;
}
