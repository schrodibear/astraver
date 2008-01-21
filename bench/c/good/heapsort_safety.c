
/* Heapsort (safety only) */

/*** arith *******************************************************************/

//@ axiom div2_1 : \forall unsigned int i; 0 <= i => 0 <= i/2 <= i

//@ axiom div2_2 : \forall unsigned int i; 0 < i => 0 <= i/2 < i

// @ axiom div2_3 : \forall int i; 0 <= i => i-1 < 2*(i/2)+1

/*****************************************************************************/

/*@ requires \valid(a+i) && \valid(a+j)
  @*/
void swap(int* a, unsigned int i, unsigned int j) {
  int tmp = a[i];
  a[i] = a[j];
  a[j] = tmp;
}

/*@ requires 
  @   0 <= low <= high && 2*high <= \max_range(unsigned int) 
  @   && \valid_range(a, low, high)
  @*/
void sift_down(int* a, unsigned int low, unsigned int high) {
  unsigned int i = low, child;
  /*@ invariant 
    @   low <= i <= high
    @ variant 
    @   high - i
    @*/
  while ((child = 2u*i+1u) <= high) {
    if (child+1 <= high && a[child+1] >= a[child]) child++;
    if (a[i] >= a[child]) break;
    swap(a, i, child);
    i = child;
  }
}

/*@ requires 
  @   0 <= n && \valid_range(a, 0, n-1)
  @*/
void heapsort(int* a, unsigned int n) {
  unsigned int i;
  if (n <= 1) return;
  /*@ invariant 
    @   0 <= i < n
    @ variant 
    @   i
    @*/
  for (i = n/2; i >= 1; i--) sift_down(a, i-1, n-1);
  /*@ invariant 
    @   0 <= i < n
    @ variant 
    @   i
    @*/
  for (i = n-1; i >= 1; i--) { swap(a, 0, i); sift_down(a, 0, i-1); }
}
