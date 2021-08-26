//@ ltl invariant negative: (<> (AP(x_2 - x_3 > 12) U (<> AP(x_0 - x_3 >= 2))));
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
x_0_ = ((2.0 + x_0) > (14.0 + x_2)? (2.0 + x_0) : (14.0 + x_2));
x_1_ = ((2.0 + x_0) > (17.0 + x_2)? (2.0 + x_0) : (17.0 + x_2));
x_2_ = ((2.0 + x_1) > (7.0 + x_3)? (2.0 + x_1) : (7.0 + x_3));
x_3_ = ((17.0 + x_0) > (4.0 + x_2)? (17.0 + x_0) : (4.0 + x_2));
x_0 = x_0_;
x_1 = x_1_;
x_2 = x_2_;
x_3 = x_3_;
  }
  return 0;
}
