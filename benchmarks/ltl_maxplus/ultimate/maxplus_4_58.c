//@ ltl invariant negative: ([] (([] AP(x_3 - x_2 > -5)) U AP(x_1 - x_2 >= -8)));
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
x_0_ = ((18.0 + x_1) > (7.0 + x_3)? (18.0 + x_1) : (7.0 + x_3));
x_1_ = ((18.0 + x_0) > (8.0 + x_3)? (18.0 + x_0) : (8.0 + x_3));
x_2_ = ((6.0 + x_2) > (19.0 + x_3)? (6.0 + x_2) : (19.0 + x_3));
x_3_ = ((1.0 + x_1) > (2.0 + x_2)? (1.0 + x_1) : (2.0 + x_2));
x_0 = x_0_;
x_1 = x_1_;
x_2 = x_2_;
x_3 = x_3_;
  }
  return 0;
}