
#pragma JessieIntegerModel(math)


/*@ requires \abs(x) <= 0x1p30;
  @ ensures \abs(\result - x) <= 1.0;
  @ behavior positive:
  @   assumes x >= 0.0;
  @   ensures 0 <= \result <= x < \result + 1;  
  @   ensures -1.0 <= \result - x <= 0.0;
  @ behavior negative:
  @   assumes x <= 0.0;
  @   ensures 0 >= \result >= x > \result - 1;  
  @   ensures 1.0 >= \result - x >= 0.0;
  @*/
int f(double x) {
  int i;
  i = x;
  return i;
}
