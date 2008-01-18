
/* Heapsort */

//@ type int_array

//@ logic int access(int_array a, int i)

//@ logic int_array contents(int* a) reads a[..]

/*@ axiom access_contents : 
  @   \forall int* a; \forall int i; access(contents(a), i) == a[i]
  @*/

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

/*@ predicate Sorted(int_array a, int l, int h) {
  @   \forall int i; l <= i < h => access(a, i) <= access(a, i+1)
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

/*@ requires \valid_range(a, root, bottom)
  @ assigns  a[root..bottom]
  @ ensures  Permut(contents(a), \old(contents(a)), root, bottom)
  @*/
void sift_down(int* a, unsigned int root, unsigned int bottom);

/*@ requires \valid_range(a, 0, n-1)
  @ ensures  Permut(contents(a), \old(contents(a)), 0, n-1)
  @*/
void heapsort(int* a, unsigned int n) {
  
}
