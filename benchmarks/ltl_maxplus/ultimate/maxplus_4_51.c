//@ ltl invariant negative: (<> ((x_2 - x_3 > 12) U (<> (x_0 - x_3 >= 2))));

int main()
{
  float v0, _x_v0;
  float v1, _x_v1;
  float v2, _x_v2;
  float v3, _x_v3;
  while(1) {
_x_v0 = ((2.0 + v0) > (14.0 + v2)? (2.0 + v0) : (14.0 + v2));
_x_v1 = ((2.0 + v0) > (17.0 + v2)? (2.0 + v0) : (17.0 + v2));
_x_v2 = ((2.0 + v1) > (7.0 + v3)? (2.0 + v1) : (7.0 + v3));
_x_v3 = ((17.0 + v0) > (4.0 + v2)? (17.0 + v0) : (4.0 + v2));
v0 = _x_v0;
v1 = _x_v1;
v2 = _x_v2;
v3 = _x_v3;
  }
  return 0;
}
