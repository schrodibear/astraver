
/* search for a value in an array */

/*@ requires \valid_range(t,0,n)
  @ ensures 
  @   (0 <= \result < n => t[\result] == v) &&
  @   (\result == n => \forall int i; 0 <= i < n => t[i] != v) 
  @*/
int index(int t[], int n, int v) {
  int i = 0;
  /*@ invariant 0 <= i && \forall int k; 0 <= k < i => t[k] != v
    variant n - i */ 
  while (i < n) {
    if (t[i] == v) break;
    i++;
  }
  return i;
}

#if 0
/* same thing, with a return instead of a break */

/*@ requires \valid_range(t,0,n)
  @ ensures 0 <= \result < n => t[\result] == v 
  @*/
int index2(int t[], int n, int v) {
  int i = 0;
  /*@ invariant 0 <= i && \forall int k; 0 <= k < i => t[k] != v
    variant n - i */
  while (i < n) {
    if (t[i] == v) return i;
    i++;
  }
  return n;
}
#endif
