//@ ltl invariant negative: (<> (X ((x_0 - x_1 > -14) && (x_0 - x_1 >= -7))));

int main()
{
  float v0, _x_v0;
  float v1, _x_v1;
  float v2, _x_v2;
  float v3, _x_v3;
  while(1) {
_x_v0 = ((19.0 + v0) > (4.0 + v1)? (19.0 + v0) : (4.0 + v1));
_x_v1 = ((20.0 + v1) > (3.0 + v2)? (20.0 + v1) : (3.0 + v2));
_x_v2 = ((2.0 + v2) > (9.0 + v3)? (2.0 + v2) : (9.0 + v3));
_x_v3 = ((19.0 + v0) > (1.0 + v3)? (19.0 + v0) : (1.0 + v3));
v0 = _x_v0;
v1 = _x_v1;
v2 = _x_v2;
v3 = _x_v3;
  }
  return 0;
}
