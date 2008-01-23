
/* Insertion sort */

#include "sorting.h"

/*@ requires \valid(a+i) && \valid(a+j)
  @ assigns  a[i], a[j]
  @ ensures  Swap(contents(a), \old(contents(a)), i, j)
  @*/
void swap(int* a, unsigned int i, unsigned int j) {
  int tmp = a[i];
  a[i] = a[j];
  a[j] = tmp;
}

/*@ requires n >= 0 && \valid_range(a, 0, n-1) 
  @ assigns  a[0..n-1]
  @ ensures  Sorted(a,0,n-1) && Permut(contents(a), \old(contents(a)), 0, n-1)
  @*/
void selection(int a[], unsigned int n) {
  unsigned int i, j, min;
  if (n <= 1) return;
  /*@ // a[0..i-1] is already sorted 
    @ invariant 
    @   0 <= i <= n-1 &&
    @   Sorted(a, 0, i-1) && 
    @   Permut(contents(a), \at(contents(a), init), 0, n-1) &&
    @   \forall integer k; \forall integer l; 
    @      0 <= k < i => i <= l < n => a[k] <= a[l]
    @ loop_assigns
    @   a[0..n-1]
    @ variant 
    @   n - i 
    @*/
  for (i = 0; i < n-1; i++) {
    /* we look for the minimum of a[i..n-1] */
    min = i; 
    /*@ invariant 
      @   i+1 <= j <= n && 
      @   i <= min < n &&
      @   \forall int k; i <= k < j => a[min] <= a[k]
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


/* test 
int main() {
  int i;
  int t[10] = { 3,5,1,0,6,8,4,2,9,7 };
  selection(t, 10);
  for (i = 0; i < 10; i++) printf("%d ", t[i]);
}
*/

/*
Local Variables: 
compile-command: "make selection.gui"
End: 
*/
