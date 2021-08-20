//@ ltl invariant negative: ((X (X (x_1 - x_2 >= 11))) U (x_1 - x_2 > 15));

int main()
{
  float v0, _x_v0;
  float v1, _x_v1;
  float v2, _x_v2;
  float v3, _x_v3;
  while(1) {
_x_v0 = ((9.0 + v1) > (6.0 + v2)? (9.0 + v1) : (6.0 + v2));
_x_v1 = ((9.0 + v1) > (17.0 + v3)? (9.0 + v1) : (17.0 + v3));
_x_v2 = ((14.0 + v0) > (6.0 + v3)? (14.0 + v0) : (6.0 + v3));
_x_v3 = ((7.0 + v1) > (11.0 + v2)? (7.0 + v1) : (11.0 + v2));
v0 = _x_v0;
v1 = _x_v1;
v2 = _x_v2;
v3 = _x_v3;
  }
  return 0;
}
