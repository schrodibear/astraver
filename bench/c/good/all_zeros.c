
/* vérifie que t[0..n-1] ne contient que des 0 */

/*@ requires \valid_range(t,0,n) 
    ensures \result <=> \forall int i; 0<=i<n => t[i]==0 */
int all_zeros(int t[], int n) {
  /*@ invariant n <= \old(n) && \forall int i; n<=i<\old(n) => t[i]==0
      variant n */
  while (--n>=0 && !t[n]);
  return n < 0;
}

#ifdef ZERO
/*@ requires \valid_range(t,0,n) 
    ensures \result <=> \forall int i; 0<=i<n => t[i]==0 */
int all_zeros_1(int t[], int n) {
  int k = 0;
  /*@ invariant 0 <= k <= n && \forall int i; 0<=i<k => t[i]==0 variant n-k */
  while (k<n && !t[k++]);
  return k == n;
}
#endif

/*@ requires \valid_range(t,0,n) 
    ensures \result <=> \forall int i; 0<=i<n => t[i]==0 */
int all_zeros_0(int t[], int n) {
  int k;
  /*@ invariant 0 <= k <= n && \forall int i; 0<=i<k => t[i]==0 variant n-k */
  for (k = 0; k < n; k++) if (t[k]) return 0;
  return 1;
}
