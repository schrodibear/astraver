
#define UPPER 0x1p340
#define LOWER 0x1p-341

/****

UPPER=0x1p341 and LOWER=0x1p-340 does not work because the division
might overflow

We need UPPER=2^u and LOWER=2^(-l) where 2*u+l < 1022

Proof :

  z - x[i-1] and y[i] - y[i-1] in [ -2 UPPER, 2 UPPER ]

  x[i] - x[i-1] >= LOWER

computation of ..* .. / .. does not overflow if  

((2 UPPER)^2) / LOWER is <= max_double = 2^1024 - 1 

ie (2^{u+1} ^ 2) / 2^(-l) < 2^1024

ie 2u+2 + l < 1024

ie 2u+l < 1022
 


*/



/*@ predicate min_step{L}(double t[], integer a, integer b, real bound) = 
  @    \forall integer i; a < i <= b ==> t[i] - t[i-1] >= bound;
  @*/

/*@ lemma min_step_increasing{L}:
  @   \forall double t[], integer a, b, real bound;
  @     bound >= 0.0 && min_step(t,a,b,bound) ==> 
  @     \forall integer i,j; 
  @          a <= i <= j <= b ==> t[i] <= t[j];
  @*/

//@ predicate bounded(double z, real bound) = -bound <= z <= bound;

/*@ predicate array_bounded{L}(double t[],int n, real bound) = 
  @   \forall integer i; 0 <= i < n ==> bounded(t[i],bound);
  @*/

//@ ghost int i_interp;

/*@ requires n >= 1 && \valid_range(x,0,n-1) && \valid_range(y,0,n-1);
  @ requires min_step(x,0,n-1,LOWER);
  @ requires bounded(z,UPPER);
  @ requires array_bounded(x,n,UPPER) ;
  @ requires array_bounded(y,n,UPPER);
  @ assigns i_interp;
  @ behavior too_low:
  @   assumes z <= x[0];
  @   ensures \result == y[0];
  @ behavior too_high:
  @   assumes z > x[n-1];
  @   ensures \result == y[n-1];
  @ behavior in_interval:
  @   assumes x[0] < z <= x[n-1]; 
  @   ensures 1 <= i_interp <= n-1;
  @   ensures x[i_interp-1] < z <= x[i_interp] ;
  @   ensures 
  @     \let v = (y[i_interp] - y[i_interp-1])/(x[i_interp]-x[i_interp-1]) ;
  @     \let exact_result = y[i_interp] + v*(z - x[i_interp-1]) ;
  @     \abs(\result - exact_result) <= 0x1p-10 ;
  @*/
double interp_lin(double x[], double y[], int n, double z) {
  int i;
  if (z <= x[0]) return y[0];

  /*@ loop invariant 1 <= i <= n;
    @ loop invariant \forall integer j; 0 <= j < i ==> z > x[j];
    @ loop variant n-i;
    @*/
  for (i=1; i<n; i++) {if (z <= x[i]) break;}
  if (i==n) return y[n-1];
  //@ ghost i_interp = i;
  double xim1 = x[i-1];
  //@ assert bounded(xim1,UPPER);
  double xi = x[i];
  //@ assert bounded(xi,UPPER);
  //@ assert xi - xim1 >= LOWER;
  double yim1 = y[i-1];
  //@ assert bounded(yim1,UPPER);
  double yi = y[i];
  //@ assert bounded(yi,UPPER);
  // @ assert \abs(yi - yim1) <= 2.0 * UPPER;
  double v = (yi-yim1)/(xi-xim1);
  // @ assert \abs(z - xim1) <= 2.0 * UPPER;
  return yi+v*(z-xim1);
}

/* 
Local Variables:
compile-command: "PPCHOME=../.. LC_ALL=C make floats_interp"
End:
*/
