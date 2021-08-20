//@ ltl invariant negative: ((x_2 - x_1 >= 4) && ([] (<> (x_2 - x_1 >= 9))));

int main()
{
  float v0, _x_v0;
  float v1, _x_v1;
  float v2, _x_v2;
  float v3, _x_v3;
  while(1) {
_x_v0 = ((9.0 + v1) > (10.0 + v2)? (9.0 + v1) : (10.0 + v2));
_x_v1 = ((16.0 + v2) > (5.0 + v3)? (16.0 + v2) : (5.0 + v3));
_x_v2 = ((6.0 + v0) > (4.0 + v1)? (6.0 + v0) : (4.0 + v1));
_x_v3 = ((6.0 + v0) > (16.0 + v1)? (6.0 + v0) : (16.0 + v1));
v0 = _x_v0;
v1 = _x_v1;
v2 = _x_v2;
v3 = _x_v3;
  }
  return 0;
}
