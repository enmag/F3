//@ ltl invariant negative: ((X AP(x_0 - x_3 > -18)) || (X AP(x_0 - x_2 > 13)));
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
x_0_ = ((13.0 + x_1) > (9.0 + x_3)? (13.0 + x_1) : (9.0 + x_3));
x_1_ = ((1.0 + x_1) > (1.0 + x_2)? (1.0 + x_1) : (1.0 + x_2));
x_2_ = ((5.0 + x_0) > (16.0 + x_2)? (5.0 + x_0) : (16.0 + x_2));
x_3_ = ((6.0 + x_1) > (14.0 + x_2)? (6.0 + x_1) : (14.0 + x_2));
x_0 = x_0_;
x_1 = x_1_;
x_2 = x_2_;
x_3 = x_3_;
  }
  return 0;
}
