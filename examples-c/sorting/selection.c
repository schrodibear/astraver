
/* Selection sort */

//@ logic intmset mset(int t[],int i,int j) reads t[*]

/*@ predicate sorted(int t[],int i,int j) {
  @   \forall int k; i <= k < j => t[k] <= t[k+1]
  @ }
  @*/

/*@ requires n >= 1 && \valid_range(t,0,n-1) 
  @ ensures sorted(t,0,n-1) && mset(t,0,n-1) == \old(mset(t,0,n-1))
  @*/
void selection(int t[],int n) {
  int i,j,min;
  int tmp;
  init:
  /*@ (* t[0..i-1] is already sorted *)
    @ invariant 
    @   0 <= i <= n-1 &&
    @   sorted(t, 0, i-1) && 
    @   mset(t,0,n-1) == \at(mset(t,0,n-1),init) &&
    @   \forall int k; \forall int l; 0 <= k < i =>
    @		  i <= l < n => t[k] <= t[l]
    @	variant n - i 
    @*/
  for (i=0; i < n-1; i++) {
    /* we look for the minimum of t[i..n-1] */
    min = i; 
    /*@ invariant 
      @   i+1 <= j <= n && 
      @   i <= min < n &&
      @   \forall int k; i <= k < j => t[min] <= t[k]
      @ variant n - j 
      @*/
    for (j = i + 1; j < n; j++) {
      if (t[j] < t[min]) min = j;
    }
    /* we swap t[i] and t[min] */
    tmp = t[min]; t[min] = t[i]; t[i] = tmp;
  }
}
