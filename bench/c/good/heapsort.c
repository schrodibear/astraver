
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

//@ predicate Permut(int_array a1, int_array a2, int n)

/*@ axiom Permut_refl: 
  @   \forall int_array a; \forall int n; Permut(a, a, n)
  @*/

/*@ axiom Permut_sym: 
  @   \forall int_array a1, int_array a2, int n; 
  @     Permut(a1, a2, n) => Permut(a2, a1, n)
  @*/

/*@ axiom Permut_trans: 
  @   \forall int_array a1, int_array a2, int_array a3, int n; 
  @     Permut(a1, a2, n) => Permut(a2, a3, n) => Permut(a1, a3, n)
  @*/

/*@ axiom Permut_swap: 
  @   \forall int_array a1, int_array a2, int n, int i, int j; 
  @     0 <= i < n => 0 <= j < n => Swap(a1, a2, i, j) => Permut(a1, a2, n)
  @*/

/*@ predicate Sorted(int_array a, int n) {
  @   \forall int i; 0 <= i < n-1 => access(a, i) <= access(a, i+1)
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

/*@ requires \valid_range(a, 0, n-1)
  @ ensures  Permut(contents(a), \old(contents(a)), n)
  @*/
void heapsort(int* a, int n) {
  
}
