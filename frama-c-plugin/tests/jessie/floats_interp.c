#pragma JessieFloatModel(strict)


#define UPPER 0x1p340
#define LOWER 0x1p-341

/****

UPPER=0x1p341 and LOWER=0x1p-340 does not work because the division
might overflow

We need UPPER=2^u and LOWER=2^(-l) where 2*u+l < 1022

Proof :

  z - x[i-1] and y[i] - y[i-1] in [ -2 UPPER, 2 UPPER ]

  x[i] - x[i-1] >= LOWER

division does not overflow if  

((2 UPPER)^2) / LOWER is <= max_double = 2^1024 - 1 

ie (2^{u+1} ^ 2) / 2^(-l) < 2^1024

ie 2u+2 + l < 1024

ie 2u+l < 1022
 


*/



/*@ predicate min_step{L}(double t[], integer a, integer b) = 
  @    \forall integer i; a < i <= b ==> t[i] - t[i-1] >= LOWER;
  @*/

/*@ lemma min_step_increasing{L}:
  @   \forall double t[], integer a, b;
  @     min_step(t,a,b) ==> \forall integer i,j; 
  @          a <= i <= j <= b ==> t[i] <= t[j];
  @*/

//@ predicate bounded(double z) = -UPPER <= z <= UPPER;

/*@ predicate array_bounded{L}(double t[],int n) = 
  @   \forall integer i; 0 <= i < n ==> bounded(t[i]);
  @*/

//@ ghost int i_interp;

/*@ requires n >= 1 && \valid_range(x,0,n-1) && \valid_range(y,0,n-1);
  @ requires min_step(x,0,n-1);
  @ requires bounded(z);
  @ requires array_bounded(x,n) ;
  @ requires array_bounded(y,n);
  @ assigns i_interp;
  @ ensures z <= x[0] ==> \result == y[0];
  @ ensures z > x[n-1] ==> \result == y[n-1];
  @ // ensures x[0] < z <= x[n-1] ==> 
  @ //           x[i_interp-1] < z <= x[i_interp] && 
  @ //           \min(y[i_interp-1],y[i_interp]) <= \result <= 
  @ //           \max(y[i_interp-1],y[i_interp]);
  @*/
double interp_lin(double x[], double y[], int n, double z) {
  int i;
  if (z <= x[0]) return y[0];

  /*@ loop invariant 1 <= i <= n;
    @ loop invariant z > x[i-1];
    @ loop variant n-i;
    @*/
  for (i=1; i<n; i++) {if (z <= x[i]) break;}
  if (i==n) return y[n-1];
  //@ assert bounded(x[i-1]);
  //@ assert bounded(x[i]);
  //@ assert bounded(y[i-1]);
  //@ assert bounded(y[i]);
  //@ assert x[i] - x[i-1] >= LOWER;
  //@ assert \abs(z - x[i-1]) <= 2.0 * UPPER;
  //@ assert \abs(y[i] - y[i-1]) <= 2.0 * UPPER;
   return y[i-1]+(z-x[i-1])*(y[i]-y[i-1])/(x[i]-x[i-1]);
}

/* 
Local Variables:
compile-command: "PPCHOME=../.. LC_ALL=C make floats_interp"
End:
*/
