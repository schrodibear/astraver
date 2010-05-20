

#pragma JessieIntegerModel(exact)

// cnt(a,n,val) returns the number of occurrences of val in a[0..n):
/*@
  axiomatic cnt_axioms
  {
    logic integer cnt{L}(int* a, integer n, int val) reads a[0..n-1] ;

    axiom cnt_empty{L}:
      \forall int* a, integer n, int val; n <= 0 ==>
         cnt(a, n, val) == 0;

    axiom cnt_hit{L}:
      \forall int* a, integer n, int val; n >= 0 && a[n] == val ==>
         cnt(a, n+1, val) == cnt(a, n, val) + 1;

    axiom cnt_miss{L}:
      \forall int* a, integer n, int val; n >= 0 && a[n] != val ==>
         cnt(a, n+1, val) == cnt(a, n, val);
   }
*/

/* useless since there is a reads clause @
  lemma cnt_footprint{L,M} :
     \forall int*a, integer n, int x; 
     (\forall integer k; 0 <= k < n ==> \at(a[k],L) == \at(a[k],M))
     ==>
     cnt{L}(a,n,x) == cnt{M}(a,n,x);
*/

/*@
  requires n >= 0;
  requires \valid_range(a, 0, n-1);
  requires \valid_range(b, 0, n-1);

  // only b[0..\result) may be modified:
  assigns b[0 .. n-1];
  ensures \forall int k; \result <= k < n ==> b[k] == \old(b[k]);

  // no occurrence of val appears in b[]:
  ensures \forall int k; 0 <= k < \result ==> b[k] != val;

  // all other values from a[] appear in b[], with same frequency:
  ensures \forall int x; x != val ==> cnt(a,n,x) == cnt(b,\result,x);

  // specify b[]'s length:
  ensures \result == n - cnt(a,n,val);
  // (include some redundancy into length spec.:)
  ensures 0 <= \result <= n;
*/



// copy a[] to b[], but skip every occurrence of val,
// return the fill-degree of b[]
int remove_copy(const int* a, int n, int* b, int val)
{
  int i;	// next uncopied elem in a[]
  int j = 0;	// next free elem in b[]

  /*@
    loop assigns b[0..j-1];

    loop invariant 0 <= j <= i <= n;

    loop invariant \forall int k; j <= k < n ==> b[k] == \at(b[k],Pre);
    loop invariant \forall int k; 0 <= k < j ==> b[k] != val;
    loop invariant \forall int x; x != val ==>
        cnt{Here}(a,i,x) == cnt{Here}(b,j,x);
    loop invariant j == i - cnt{Here}(a,i,val);
    loop   variant n-i;
  */

  for (i=0; i<n; ++i)
    if (a[i] != val) {
      // (*1)
    Before:
      b[j] = a[i];
      // @ assert \forall int x; x != val ==> cnt{Here}(a,i,x) == cnt{Here}(b,j,x);
      // (*2)
      j++;
    }
  return j;
}
