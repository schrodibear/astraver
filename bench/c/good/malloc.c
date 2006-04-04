
/*@ requires 
  @   n >= 1 
  @ ensures 
  @   \valid_range(\result,0,n-1) && 
  @   \forall int i; 0<=i<n => \valid(\result[i]) */
int** test(int n) { 
  int** t = (int**)malloc(n * sizeof(int*));
  int i;
  /*@ invariant 
    @   0 <= i <= n && \forall int k; 0<=k<i => \valid(t[k]) */
  for (i = 0; i < n; i++)
    t[i] = (int*)malloc(sizeof(int));
  return t;
}

//@ ensures \result == 0
int main() {
  int** t = test(10);
  t[3][0] = 0;
  // t[4][0] = 1;
  return t[3][0];
}
