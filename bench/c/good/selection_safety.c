
/* Insertion sort (safety only; for correctness proof, see selection.c) */

/*@ requires \valid(a+i) && \valid(a+j)
  @*/
void swap(int* a, unsigned int i, unsigned int j) {
  int tmp = a[i];
  a[i] = a[j];
  a[j] = tmp;
}

/*@ requires n >= 0 && \valid_range(a, 0, n-1) 
  @*/
void selection(int a[], unsigned int n) {
  unsigned int i, j, min;
  if (n <= 1) return;
  /*@ // a[0..i-1] is already sorted 
    @ invariant 
    @   0 <= i <= n-1
    @ variant 
    @   n - i 
    @*/
  for (i = 0; i < n-1; i++) {
    /* we look for the minimum of a[i..n-1] */
    min = i; 
    /*@ invariant 
      @   i+1 <= j <= n &&
      @   i <= min < n 
      @ variant 
      @   n - j 
      @*/
    for (j = i + 1; j < n; j++) {
      if (a[j] < a[min]) min = j;
    }
    /* we swap a[i] and a[min] */
    swap(a,min,i);
  }
}


/*
Local Variables: 
compile-command: "make selection_safety.overflows"
End: 
*/
