
float f;
double d;
long double l;

/*@ requires f == 0 + 1.0
  @ ensures  d >= 1 - 2.34
  @*/
void f1() { 
  f = 0;
  d = f + 1.0;
  l = f + d + 3;
}

/*@ requires x == \exact(x) && |x| <= 1
  @ ensures  \round_error(\result) <= 2 ^^ (-48)
  @*/
double my_exp(double x) {
  return 1 + x + x*x/2;
}

