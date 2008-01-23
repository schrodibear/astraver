
/* Insertion sort (safety only; for correctness proof, see insertion.c) */

/*@ requires 
  @   0 <= n && \valid_range(a, 0, n-1)
  @*/
void insertion_sort(int* a, unsigned int n) {
  unsigned int i;
  if (n <= 1) return;
  /*@ invariant
    @   0 < i <= n
    @ variant
    @   n - i
    @*/
  for (i = 1; i < n; i++) {
    int v = a[i];
    unsigned int j = i;
    /*@ invariant
      @   0 <= j <= i
      @ variant
      @   j
      @*/
    while (j > 0 && a[j-1] > v) { a[j] = a[j-1]; j--; }
    a[j] = v;
  }
}


/*
Local Variables: 
compile-command: "make insertion_safety.overflows"
End: 
*/
