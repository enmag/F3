//@ ltl invariant negative: ((X (X (x_3 - x_2 > -18))) U (x_2 - x_3 >= 13));

int main()
{
  float v0, _x_v0;
  float v1, _x_v1;
  float v2, _x_v2;
  float v3, _x_v3;
  while(1) {
_x_v0 = ((8.0 + v0) > (8.0 + v1)? (8.0 + v0) : (8.0 + v1));
_x_v1 = ((13.0 + v2) > (8.0 + v3)? (13.0 + v2) : (8.0 + v3));
_x_v2 = ((4.0 + v0) > (13.0 + v2)? (4.0 + v0) : (13.0 + v2));
_x_v3 = ((13.0 + v0) > (17.0 + v2)? (13.0 + v0) : (17.0 + v2));
v0 = _x_v0;
v1 = _x_v1;
v2 = _x_v2;
v3 = _x_v3;
  }
  return 0;
}
