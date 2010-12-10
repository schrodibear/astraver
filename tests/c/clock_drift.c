// RUNGAPPA: will ask regtests to run gappa on VCs of this program

#define NMAX 1000000
#define NMAXR 1000000.0

// this one is needed by Gappa to prove the assertion on the rounding error
/*@ lemma real_of_int_inf_NMAX:
  @   \forall integer i; i <= NMAX ==> i <= NMAXR;
  @*/

// this one does not seem useful for Alt-Ergo
// but it is for CVC3, to prove preservation of the loop
// invariant. Z3 does not prove it either
//@ lemma real_of_int_succ: \forall integer n; n+1 == n + 1.0;

// this one does not seem to be needed anymore
/* lemma inf_mult : 
  @    \forall real x,y,z; x<=y && 0<=z ==> x*z <= y*z;
  @*/

#define A 1.49012e-09 
// A is a bound of (float)0.1 - 0.1

// this one is not needed anymore since (float)0.1 is evaluated
// at compile-time
// lemma round01: \abs((float)0.1 - 0.1) <=  A;

// B is a bound of round_error(t+(float)0.1) for 0 <= t <= 0.1*NMAXR
// NMAX = 100 -> #define B 4.76838e-07
// NMAX = 1000000 ->
#define B 0x1p-8

#define C (B + A)

/*@ requires 0 <= n <= NMAX;
  @ ensures \abs(\result - n*0.1) <= n * C;
  @*/
float f_single(int n)
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

