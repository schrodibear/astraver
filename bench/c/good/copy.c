
/* array copy */

/*@ requires \valid_range(t1,0,n) && \valid_range(t2,0,n) &&
  @   \base_addr(t1) != \base_addr(t2)
  @ ensures \forall int k; 0 <= k < n => t2[k] == t1[k]
  @*/
void copy(int t1[], int t2[], int n) {
  int i = n;
  /*@ invariant i <= n && \forall int k; i <= k < n => t2[k] == t1[k]
      variant i */   
  while (i-- > 0) {
    t2[i] = t1[i];
  }
}

