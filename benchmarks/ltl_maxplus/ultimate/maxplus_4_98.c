//@ ltl invariant negative: ((X AP(x_3 - x_0 >= -20)) R (<> AP(x_3 - x_1 >= 3)));
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
x_0_ = ((14.0 + x_0) > (6.0 + x_2)? (14.0 + x_0) : (6.0 + x_2));
x_1_ = ((13.0 + x_0) > (17.0 + x_1)? (13.0 + x_0) : (17.0 + x_1));
x_2_ = ((18.0 + x_0) > (5.0 + x_3)? (18.0 + x_0) : (5.0 + x_3));
x_3_ = ((11.0 + x_1) > (12.0 + x_3)? (11.0 + x_1) : (12.0 + x_3));
x_0 = x_0_;
x_1 = x_1_;
x_2 = x_2_;
x_3 = x_3_;
  }
  return 0;
}
