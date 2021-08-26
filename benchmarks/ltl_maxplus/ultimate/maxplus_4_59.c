//@ ltl invariant negative: (AP(x_3 - x_2 >= 14) || (X (<> AP(x_2 - x_1 >= -1))));
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
x_0_ = ((8.0 + x_2) > (1.0 + x_3)? (8.0 + x_2) : (1.0 + x_3));
x_1_ = ((14.0 + x_1) > (1.0 + x_3)? (14.0 + x_1) : (1.0 + x_3));
x_2_ = ((1.0 + x_0) > (4.0 + x_1)? (1.0 + x_0) : (4.0 + x_1));
x_3_ = ((2.0 + x_0) > (1.0 + x_2)? (2.0 + x_0) : (1.0 + x_2));
x_0 = x_0_;
x_1 = x_1_;
x_2 = x_2_;
x_3 = x_3_;
  }
  return 0;
}
