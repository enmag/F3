//@ ltl invariant negative: (AP(x_0 - x_3 > 17) R (X (X AP(x_3 - x_1 > -16))));
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
x_0_ = ((20.0 + x_1) > (14.0 + x_2)? (20.0 + x_1) : (14.0 + x_2));
x_1_ = ((8.0 + x_0) > (11.0 + x_1)? (8.0 + x_0) : (11.0 + x_1));
x_2_ = ((14.0 + x_1) > (2.0 + x_3)? (14.0 + x_1) : (2.0 + x_3));
x_3_ = ((2.0 + x_1) > (9.0 + x_2)? (2.0 + x_1) : (9.0 + x_2));
x_0 = x_0_;
x_1 = x_1_;
x_2 = x_2_;
x_3 = x_3_;
  }
  return 0;
}
