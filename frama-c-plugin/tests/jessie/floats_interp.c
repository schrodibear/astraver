#pragma JessieFloatModel(strict)

/*@ predicate sorted{L}(double t[], integer a, integer b) = 
  @    \forall integer i,j; a <= i <= j <= b ==> t[i] <= t[j];
  @*/

//@ predicate bounded(double z) = -0x1p24 <= z <= 0x1p24;

/*@ predicate array_bounded{L}(double t[],int n) = 
  @   \forall integer i; 0 <= i < n ==> bounded(t[i]);
  @*/

/*@ requires n >= 1 && \valid_range(x,0,n-1) && \valid_range(y,0,n-1);
  @ requires bounded(z);
  @ requires array_bounded(x,n) && array_bounded(y,n);
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
  //@ assert x[i-1] <= z <= x[i];
  //@ assert bounded(z);
  //@ assert bounded(x[i-1]);
  //@ assert bounded(y[i-1]);
  //@ assert bounded(x[i]);
  //@ assert bounded(y[i]);
  return y[i-1]+(z-x[i-1])*(y[i]-y[i-1])/(x[i]-x[i-1]);
}

/* 
Local Variables:
compile-command: "PPCHOME=../.. LC_ALL=C make floats_bsearch"
End:
*/
