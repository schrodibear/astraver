
//@ type int_array

//@ logic integer access(int_array a, integer i)

//@ logic int_array contents(int* a) reads a[..]

//@ logic int_array update(int_array a, integer i, integer v)

/*@ axiom access_update_eq : 
  @   \forall int_array a, integer i, integer v; 
  @      access(update(a, i, v), i) == v
  @*/

/*@ axiom access_update_neq : 
  @   \forall int_array a, integer i, integer j, integer v; 
  @      i != j => access(update(a, i, v), j) == access(a, j)
  @*/

/*@ axiom access_contents : 
  @   \forall int* a; \forall integer i; access(contents(a), i) == a[i]
  @*/

/*** permutation ************************************************************/

/*@ predicate Swap(int_array a1, int_array a2, integer i, integer j) {
  @   access(a1, i) == access(a2, j) &&
  @   access(a1, j) == access(a2, i) &&
  @   \forall integer k; k != i => k != j => access(a1, k) == access(a2, k)
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

