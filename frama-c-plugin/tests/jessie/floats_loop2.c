#define NMAX 1000000
#define NMAXR 1000000.0

/***********
TODO:

. axiomes sur real_of_int dans real.why

. axiome round(f,m,0.0) == 0.0

**********/

/*@ lemma real_of_int_inf_NMAX: 
  @   \forall integer i; i <= NMAX ==> i <= NMAXR;
  @*/

//@ lemma real_of_int_succ: \forall integer n; n+1 == n + 1.0;

/*@ lemma inf_mult : 
  @    \forall real x,y,z; x<=y && 0<=z ==> x*z <= y*z;
  @*/

#define A 1.49012e-09 
// A is a bound of (float)0.1 - 0.1

//@ lemma round01: \abs((float)0.1 - 0.1) <=  A;

// B is a bound of round_error(t+(float)0.1) for 0 <= t <= 0.1*NMAXR
// NMAX = 100 -> #define B 4.76838e-07
// NMAX = 1000000 ->
#define B 0x1p-8

#define C (B + A)

/*@ requires 0 <= n <= NMAX;
  @ ensures \abs(\result - n*0.1) <= n * C;
  @*/
float f(int n)
{
  float t = 0.0f;
  int i;

  /*@ loop invariant 0 <= i <= n;
    @ loop invariant \abs(t - i * 0.1) <= i * C ;
    @ loop variant n-i;
    @*/
  for(i=0;i<n;i++) {
  L:
    //@ assert 0.0 <= t <= NMAXR*(0.1+C)  ;
    t = t + 0.1f;
    //@ assert \abs(t - (\at(t,L) + (float)0.1)) <=  B;
  }
  return t;
}

























#if 0
//@ ensures \result < 1.0;
double f_double()
{
  double t = 0.0;
  int i;
  /*@ loop invariant i <= 10;
    @ loop invariant t <= i * 0.09999999999999999;
    @ loop variant 10-i;
    @*/
  for(i=0;i<10;i++) t = t + 0.1;
  return t;
}
#endif


int main() {
  f_single(100);
  //printf("float: %20.15f\n", f_single(100));   
  /*
  printf("double: %30.25f\n", f_double(100)); 
  */
  return 0;
}

