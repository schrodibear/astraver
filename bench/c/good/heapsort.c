
/* Heapsort */

//@ type int_array

//@ logic int access(int_array a, int i)

//@ logic int_array contents(int* a) reads a[..]

/*@ axiom access_contents : 
  @   \forall int* a; \forall int i; access(contents(a), i) == a[i]
  @*/

/*** permutation ************************************************************/

/*@ predicate Swap(int_array a1, int_array a2, int i, int j) {
  @   access(a1, i) == access(a2, j) &&
  @   access(a1, j) == access(a2, i) &&
  @   \forall int k; k != i => k != j => access(a1, k) == access(a2, k)
  @ }
  @*/

//@ predicate Permut(int_array a1, int_array a2, int l, int h)

/*@ axiom Permut_refl: 
  @   \forall int_array a; \forall int l, int h; Permut(a, a, l, h)
  @*/

/*@ axiom Permut_sym: 
  @   \forall int_array a1, int_array a2, int l, int h; 
  @     Permut(a1, a2, l, h) => Permut(a2, a1, l, h)
  @*/

/*@ axiom Permut_trans: 
  @   \forall int_array a1, int_array a2, int_array a3, int l, int h; 
  @     Permut(a1, a2, l, h) => Permut(a2, a3, l, h) => Permut(a1, a3, l, h)
  @*/

/*@ axiom Permut_swap: 
  @   \forall int_array a1, int_array a2, int l, int h, int i, int j; 
  @   l <= i <= h => l <= j <= h => Swap(a1, a2, i, j) => Permut(a1, a2, l, h)
  @*/

/*@ axiom Permut_extend: 
  @   \forall int_array a1, int_array a2, int l, int h, int ll, int hh; 
  @     Permut(a1, a2, l, h) => ll <= l => h <= hh => Permut(a1, a2, ll, hh)
  @*/

/*** sorted property *********************************************************/

/*@ predicate Sorted(int* a, int l, int h) {
  @   \forall int i; l <= i < h => a[i] <= a[i+1]
  @ }
  @*/

/*** heap property ***********************************************************/

/*@ predicate Hnode(int* a, int i, int h) {
  @   (2*i+1 <= h => a[i] >= a[2*i+1]) &&
  @   (2*i+2 <= h => a[i] >= a[2*i+2]) 
  @ }
  @*/

/*@ predicate H(int* a, int l, int h) {
  @   \forall int i; l <= i <= h => Hnode(a, i, h)
  @ }
  @*/

//@ axiom H_init: \forall int* a, int l, int h; l <= h < 2*l+1 => H(a, l, h)

// @ axiom H_reduce: \forall int* a, int h; 0 < h => H(a, 0, h) => H(a, 1, h-1)

/*@ axiom H_max: 
  @   \forall int* a, int h; 
  @     H(a, 0, h) => \forall int i; 0 <= i <= h => a[0] >= a[i]
  @*/

/*** arith *******************************************************************/

//@ axiom div2_1 : \forall int i; 0 <= i => 0 <= i/2 <= i

//@ axiom div2_2 : \forall int i; 0 < i => 0 <= i/2 < i

//@ axiom div2_3 : \forall int i; 0 <= i => i-1 < 2*(i/2)+1

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

/*@ requires 
  @   0 <= low <= high && \valid_range(a, low, high) && H(a, low+1, high)
  @ assigns  
  @   a[low..high]
  @ ensures  
  @   Permut(contents(a), \old(contents(a)), low, high) && H(a, low, high)
  @*/
void sift_down(int* a, unsigned int low, unsigned int high) {
  unsigned int i = low, child;
  /*@ invariant 
    @   low <= i <= high && 
    @   Permut(contents(a), \at(contents(a), init), low, high) &&
    @   (\forall int k; low <= k <= high => k != i => Hnode(a, k, high)) &&
    @   ((low < i && low <= (i-1)/2) => 
    @      ((2*i+1 <= high => a[(i-1)/2] >= a[2*i+1]) &&
    @       (2*i+2 <= high => a[(i-1)/2] >= a[2*i+2])))
    @ loop_assigns
    @   a[low..high]
    @ variant 
    @   high - i
    @*/
  while ((child = 2*i+1) <= high) {
    if (child+1 <= high && a[child+1] >= a[child]) child++;
    if (a[i] >= a[child]) break;
    swap(a, i, child);
    i = child;
  }
}

/*@ requires 
  @   0 <= n && \valid_range(a, 0, n-1)
  @ ensures  
  @   Permut(contents(a), \old(contents(a)), 0, n-1) && Sorted(a, 0, n-1)
  @*/
void heapsort(int* a, unsigned int n) {
  unsigned int i;
  if (n <= 1) return;
  /*@ invariant 
    @   0 <= i < n && Permut(contents(a), \at(contents(a), init), 0, n-1) &&
    @   H(a, i, n-1)
    @ variant i
    @*/
  for (i = n/2; i >= 1; i--) sift_down(a, i-1, n-1);
  /*@ invariant 
    @   0 <= i < n && Permut(contents(a), \at(contents(a), init), 0, n-1) &&
    @   H(a, 0, i) && Sorted(a, i+1, n-1) &&
    @   \forall int k1, int k2; 0 <= k1 <= i => i < k2 < n => a[k1] <= a[k2]
    @ variant i
    @*/
  for (i = n-1; i >= 1; i--) { 
    swap(a, 0, i); 
    //@ assert H(a, 1, i-1)
    sift_down(a, 0, i-1); 
  }
}
