//@ ltl invariant negative: ((x_2 - x_0 >= 3) R ((x_2 - x_0 >= -20) R (x_0 - x_1 > -15)));

int main()
{
  float v0, _x_v0;
  float v1, _x_v1;
  float v2, _x_v2;
  float v3, _x_v3;
  while(1) {
_x_v0 = ((1.0 + v0) > (8.0 + v2)? (1.0 + v0) : (8.0 + v2));
_x_v1 = ((8.0 + v0) > (9.0 + v3)? (8.0 + v0) : (9.0 + v3));
_x_v2 = ((15.0 + v0) > (4.0 + v3)? (15.0 + v0) : (4.0 + v3));
_x_v3 = ((1.0 + v1) > (11.0 + v2)? (1.0 + v1) : (11.0 + v2));
v0 = _x_v0;
v1 = _x_v1;
v2 = _x_v2;
v3 = _x_v3;
  }
  return 0;
}
