//@ ltl invariant negative: (AP(x_0 - x_3 >= -12) && (AP(x_0 - x_3 >= 6) || AP(x_0 - x_3 >= -12)));
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
x_0_ = ((16.0 + x_1) > (13.0 + x_3)? (16.0 + x_1) : (13.0 + x_3));
x_1_ = ((4.0 + x_0) > (9.0 + x_1)? (4.0 + x_0) : (9.0 + x_1));
x_2_ = ((16.0 + x_1) > (17.0 + x_3)? (16.0 + x_1) : (17.0 + x_3));
x_3_ = ((4.0 + x_1) > (15.0 + x_2)? (4.0 + x_1) : (15.0 + x_2));
x_0 = x_0_;
x_1 = x_1_;
x_2 = x_2_;
x_3 = x_3_;
  }
  return 0;
}
