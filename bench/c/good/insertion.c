
/* Insertion sort */

//@ type int_array

//@ logic int access(int_array a, integer i)

//@ logic int_array update(int_array a, integer i, int v)

/*@ axiom access_update_eq : 
  @   \forall int_array a, integer i, int v; access(update(a, i, v), i) == v
  @*/

/*@ axiom access_update_neq : 
  @   \forall int_array a, integer i, integer j, int v; 
  @      i != j => access(update(a, i, v), j) == access(a, j)
  @*/

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

/*****************************************************************************/

/*@ requires 
  @   0 <= n && \valid_range(a, 0, n-1)
  @ ensures  
  @   Permut(contents(a), \old(contents(a)), 0, n-1) && 
  @   Sorted(a, 0, n-1)
  @*/
void insertion_sort(int* a, unsigned int n) {
  unsigned int i;
  if (n <= 1) return;
}

/* test 
int main() {
  int i;
  int t[10] = { 3,5,1,0,6,8,4,2,9,7 };
  insertion_sort(t, 10);
  for (i = 0; i < 10; i++) printf("%d ", t[i]);
}
*/
