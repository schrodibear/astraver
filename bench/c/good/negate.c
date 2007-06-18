
/*@ requires n >= 0 && \valid_range(t,0,n-1)
  @ assigns t[0..n-1]
  @ ensures \forall int k; 0 <= k < n => t[k] == -\old(t[k])
  @*/
void negate(int *t, int n) {
  int i = 0;
  /*@ invariant 
    @   0 <= i <= n && 
    @   (\forall int k; 0 <= k < i => t[k] == -\old(t[k])) &&
    @   (\forall int k; i <= k < n => t[k] == \old(t[k]))
    @ loop_assigns t[0..n-1]
    @ variant n-i */
  while (i < n) {
    t[i] = -t[i];
    i++;
  }
}
