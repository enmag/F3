//@ ltl invariant negative: (AP(x_2 - x_3 >= -15) && (AP(x_1 - x_3 >= -3) U AP(x_0 - x_2 > 11)));
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
x_0_ = ((13.0 + x_2) > (18.0 + x_3)? (13.0 + x_2) : (18.0 + x_3));
x_1_ = ((10.0 + x_0) > (11.0 + x_3)? (10.0 + x_0) : (11.0 + x_3));
x_2_ = ((20.0 + x_1) > (18.0 + x_3)? (20.0 + x_1) : (18.0 + x_3));
x_3_ = ((5.0 + x_0) > (17.0 + x_2)? (5.0 + x_0) : (17.0 + x_2));
x_0 = x_0_;
x_1 = x_1_;
x_2 = x_2_;
x_3 = x_3_;
  }
  return 0;
}
