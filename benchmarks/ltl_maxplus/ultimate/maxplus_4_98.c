//@ ltl invariant negative: ((X (x_3 - x_0 >= -20)) R (<> (x_3 - x_1 >= 3)));

int main()
{
  float v0, _x_v0;
  float v1, _x_v1;
  float v2, _x_v2;
  float v3, _x_v3;
  while(1) {
_x_v0 = ((14.0 + v0) > (6.0 + v2)? (14.0 + v0) : (6.0 + v2));
_x_v1 = ((13.0 + v0) > (17.0 + v1)? (13.0 + v0) : (17.0 + v1));
_x_v2 = ((18.0 + v0) > (5.0 + v3)? (18.0 + v0) : (5.0 + v3));
_x_v3 = ((11.0 + v1) > (12.0 + v3)? (11.0 + v1) : (12.0 + v3));
v0 = _x_v0;
v1 = _x_v1;
v2 = _x_v2;
v3 = _x_v3;
  }
  return 0;
}
