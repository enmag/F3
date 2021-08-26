//@ ltl invariant negative: (X (AP(x_1 - x_3 >= -3) || ([] AP(x_2 - x_1 > 7))));
float x_0;
float x_1;
float x_2;
float x_3;
int main()
{
  float x_0_;
  float x_1_;
  float x_2_;
  float x_3_;
  while(1) {
x_0_ = ((15.0 + x_2) > (2.0 + x_3)? (15.0 + x_2) : (2.0 + x_3));
x_1_ = ((5.0 + x_0) > (17.0 + x_2)? (5.0 + x_0) : (17.0 + x_2));
x_2_ = ((17.0 + x_1) > (14.0 + x_3)? (17.0 + x_1) : (14.0 + x_3));
x_3_ = ((10.0 + x_2) > (13.0 + x_3)? (10.0 + x_2) : (13.0 + x_3));
x_0 = x_0_;
x_1 = x_1_;
x_2 = x_2_;
x_3 = x_3_;
  }
  return 0;
}
