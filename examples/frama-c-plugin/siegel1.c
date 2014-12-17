

/*@ axiomatic sums {
  @   logic real sum{L}(double *a, integer n);
  @   axiom sum1{L}: \forall double *a, integer n; n>=1 ==> 
  @     sum{L}(a,n) == \round_float(\Double,\NearestEven,sum{L}(a,n-1)+a[n-1]);
  @   axiom sum0{L}: \forall double *a; sum{L}(a,0)==0.0;
  @ }
  @*/

/*@ requires n >= 1 && \valid(t+(0..n-1));
  @ ensures \result == (double)(sum(t,n)/n);
  @ assigns \nothing;
  @*/
double mean(double *t, int n) {
  int i;
  double s = 0.0;

  /*@ loop invariant 0<=i<=n;
    @ loop invariant \valid(t+(0..n-1));
    @ loop invariant s==sum(t,i);
    @ loop assigns s;
    @ loop variant n-i;
    @*/
  for (i=0; i<n; i++) 
    s += t[i];
  return s/n;
}
