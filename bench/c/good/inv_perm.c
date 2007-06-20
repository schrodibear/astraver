
/* Inverse of a permutation, in place.
   The Art of Computer Programming, vol. 1, page 176 */

/*@ requires 
  @   n >= 0 && \valid_range(t,1,n) &&
  @   \forall int k; 1 <= k <= n => 1 <= t[k] <= n
  @*/
void inverse(int *t, int n) {
  int m = n, j = -1;
  /*@ invariant 0 <= m <= n 
    @*/
  while (m > 0) {
    int i = t[m];
    /*@ invariant 1 <= m <= n && i == t[m]
      @*/
    while (i > 0) {
      t[m] = j;
      j = -m;
      m = i;
      i = t[m];
    }
    i = j;
    t[m] = -i;
    m--;
  }
}

