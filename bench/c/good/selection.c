
/* Insertion sort */

//@ type int_array

//@ logic int access(int_array a, integer i)

//@ logic int_array contents(int* a) reads a[..]

/*@ axiom access_contents : 
  @   \forall int* a; \forall int i; access(contents(a), i) == a[i]
  @*/

/*** permutation ************************************************************/

/*@ predicate Swap(int_array a1, int_array a2, integer i, integer j) {
  @   access(a1, i) == access(a2, j) &&
  @   access(a1, j) == access(a2, i) &&
  @   \forall int k; k != i => k != j => access(a1, k) == access(a2, k)
  @ }
  @*/

//@ predicate Permut(int_array a1, int_array a2, integer l, integer h)

/*@ axiom Permut_refl: 
  @   \forall int_array a; \forall integer l, integer h; Permut(a, a, l, h)
  @*/

/*@ axiom Permut_sym: 
  @   \forall int_array a1, int_array a2, integer l, integer h; 
  @     Permut(a1, a2, l, h) => Permut(a2, a1, l, h)
  @*/

/*@ axiom Permut_trans: 
  @   \forall int_array a1, int_array a2, int_array a3, integer l, integer h; 
  @     Permut(a1, a2, l, h) => Permut(a2, a3, l, h) => Permut(a1, a3, l, h)
  @*/

/*@ axiom Permut_swap: 
  @   \forall int_array a1, int_array a2;
  @   \forall integer l, integer h, integer i, integer j; 
  @   l <= i <= h => l <= j <= h => Swap(a1, a2, i, j) => Permut(a1, a2, l, h)
  @*/

/*** sorted property *********************************************************/

/*@ predicate Sorted(int* a, integer l, integer h) {
  @   \forall integer i; l <= i < h => a[i] <= a[i+1]
  @ }
  @*/

/*****************************************************************************/

/*@ requires \valid(a+i) && \valid(a+j)
  @ assigns  a[i], a[j]
  @ ensures  Swap(contents(a), \old(contents(a)), i, j)
  @*/
void swap(int* a, int i, int j) {
  int tmp = a[i];
  a[i] = a[j];
  a[j] = tmp;
}

/*@ requires n >= 1 && \valid_range(a, 0, n-1) 
  @ assigns  a[0..n-1]
  @ ensures  Sorted(a,0,n-1) && Permut(contents(a), \old(contents(a)), 0, n-1)
  @*/
void selection(int a[], unsigned int n) {
  unsigned int i, j, min;
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
  insertion_sort(t, 10);
  for (i = 0; i < 10; i++) printf("%d ", t[i]);
}
*/
