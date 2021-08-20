//@ ltl invariant negative: ((x_2 - x_1 >= -13) || ((x_1 - x_2 > 19) R (x_1 - x_3 > 4)));

int main()
{
  float v0, _x_v0;
  float v1, _x_v1;
  float v2, _x_v2;
  float v3, _x_v3;
  while(1) {
_x_v0 = ((8.0 + v2) > (9.0 + v3)? (8.0 + v2) : (9.0 + v3));
_x_v1 = ((6.0 + v1) > (5.0 + v2)? (6.0 + v1) : (5.0 + v2));
_x_v2 = ((19.0 + v0) > (17.0 + v3)? (19.0 + v0) : (17.0 + v3));
_x_v3 = ((12.0 + v1) > (3.0 + v3)? (12.0 + v1) : (3.0 + v3));
v0 = _x_v0;
v1 = _x_v1;
v2 = _x_v2;
v3 = _x_v3;
  }
  return 0;
}
