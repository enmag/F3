//@ ltl invariant negative: ((x_1 - x_2 >= -1) && (X (<> (x_1 - x_3 > 2))));

int main()
{
  float v0, _x_v0;
  float v1, _x_v1;
  float v2, _x_v2;
  float v3, _x_v3;
  while(1) {
_x_v0 = ((5.0 + v1) > (10.0 + v3)? (5.0 + v1) : (10.0 + v3));
_x_v1 = ((5.0 + v2) > (1.0 + v3)? (5.0 + v2) : (1.0 + v3));
_x_v2 = ((20.0 + v0) > (2.0 + v2)? (20.0 + v0) : (2.0 + v2));
_x_v3 = ((10.0 + v0) > (18.0 + v1)? (10.0 + v0) : (18.0 + v1));
v0 = _x_v0;
v1 = _x_v1;
v2 = _x_v2;
v3 = _x_v3;
  }
  return 0;
}
