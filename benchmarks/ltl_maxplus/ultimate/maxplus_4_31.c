//@ ltl invariant negative: (AP(x_0 - x_1 >= -4) R (AP(x_3 - x_2 >= 14) || AP(x_2 - x_1 >= -7)));
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
x_0_ = ((16.0 + x_1) > (12.0 + x_3)? (16.0 + x_1) : (12.0 + x_3));
x_1_ = ((9.0 + x_1) > (18.0 + x_2)? (9.0 + x_1) : (18.0 + x_2));
x_2_ = ((18.0 + x_0) > (8.0 + x_1)? (18.0 + x_0) : (8.0 + x_1));
x_3_ = ((5.0 + x_0) > (16.0 + x_1)? (5.0 + x_0) : (16.0 + x_1));
x_0 = x_0_;
x_1 = x_1_;
x_2 = x_2_;
x_3 = x_3_;
  }
  return 0;
}
