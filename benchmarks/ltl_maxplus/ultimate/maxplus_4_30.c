//@ ltl invariant negative: ((X (x_3 - x_1 >= -20)) U ([] (x_2 - x_1 >= 10)));

int main()
{
  float v0, _x_v0;
  float v1, _x_v1;
  float v2, _x_v2;
  float v3, _x_v3;
  while(1) {
_x_v0 = ((17.0 + v0) > (4.0 + v2)? (17.0 + v0) : (4.0 + v2));
_x_v1 = ((7.0 + v0) > (12.0 + v3)? (7.0 + v0) : (12.0 + v3));
_x_v2 = ((8.0 + v1) > (9.0 + v2)? (8.0 + v1) : (9.0 + v2));
_x_v3 = ((14.0 + v0) > (4.0 + v1)? (14.0 + v0) : (4.0 + v1));
v0 = _x_v0;
v1 = _x_v1;
v2 = _x_v2;
v3 = _x_v3;
  }
  return 0;
}
