//@ ltl invariant negative: ((x_2 - x_1 >= 1) || (X (<> (x_2 - x_1 >= 9))));

int main()
{
  float v0, _x_v0;
  float v1, _x_v1;
  float v2, _x_v2;
  float v3, _x_v3;
  while(1) {
_x_v0 = ((6.0 + v1) > (17.0 + v3)? (6.0 + v1) : (17.0 + v3));
_x_v1 = ((2.0 + v0) > (20.0 + v3)? (2.0 + v0) : (20.0 + v3));
_x_v2 = ((8.0 + v0) > (14.0 + v1)? (8.0 + v0) : (14.0 + v1));
_x_v3 = ((18.0 + v1) > (16.0 + v2)? (18.0 + v1) : (16.0 + v2));
v0 = _x_v0;
v1 = _x_v1;
v2 = _x_v2;
v3 = _x_v3;
  }
  return 0;
}
