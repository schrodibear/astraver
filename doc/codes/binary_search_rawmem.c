//@ requires n >= 0 && \valid_range(t,0,n-1);
int binary_search(long t[], int n, long v) {
  int l = 0, u = n-1;
  //@ loop invariant 0 <= l && u <= n-1;
  while (l <= u ) {
    ...
