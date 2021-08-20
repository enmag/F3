//@ ltl invariant negative: ((<> (X (x_3 - x_0 >= -14))) R (x_2 - x_0 >= -20));

int main()
{
  float v0, _x_v0;
  float v1, _x_v1;
  float v2, _x_v2;
  float v3, _x_v3;
  while(1) {
_x_v0 = ((8.0 + v1) > (18.0 + v3)? (8.0 + v1) : (18.0 + v3));
_x_v1 = ((11.0 + v0) > (9.0 + v2)? (11.0 + v0) : (9.0 + v2));
_x_v2 = ((2.0 + v2) > (1.0 + v3)? (2.0 + v2) : (1.0 + v3));
_x_v3 = ((17.0 + v1) > (12.0 + v3)? (17.0 + v1) : (12.0 + v3));
v0 = _x_v0;
v1 = _x_v1;
v2 = _x_v2;
v3 = _x_v3;
  }
  return 0;
}
