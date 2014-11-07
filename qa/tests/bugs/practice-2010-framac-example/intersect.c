
#include "intersect.h"

/*@ axiomatic UnsignedMin {
  @   logic unsigned umin(unsigned n1,unsigned n2) = (n1 < n2) ? n1 : n2;
  @ }
  @*/

/*@ axiomatic IntSetTheory {
  @ type int_set;
  @
  @ logic int_set empty_int_set;
  @ logic int_set add_int_set(int_set s, int i);
  @ logic boolean isin_int_set(int_set s, int i);
  @ logic int_set intersect_int_set(int_set s1, int_set s2);
  @ logic integer size_int_set(int_set s1);
  @
  @ axiom add2_set:
  @  \forall int_set s, int i; add_int_set(add_int_set(s,i),i) == add_int_set(s,i);
  @
  @ axiom add_int_set_trans:
  @  \forall int_set s, int i, int j; add_int_set(add_int_set(s,i),j) == add_int_set(add_int_set(s,j),i);
  @
  @ axiom isin_empty_set:
  @  \forall int i; isin_int_set(empty_int_set,i) == \false;
  @
  @ axiom isin_add_int_set1:
  @  \forall int_set s, int i; isin_int_set(add_int_set(s,i),i);
  @
  @ axiom isin_add_int_set2:
  @  \forall int_set s, int i, int j; (i != j) ==> (isin_int_set(add_int_set(s,i),j) == isin_int_set(s,j));
  @
  @ axiom intersect_com:
  @  \forall int_set s1, int_set s2; intersect_int_set(s1,s2) == intersect_int_set(s2,s1);
  @
  @ axiom intersect_trans:
  @  \forall int_set s1, int_set s2, int_set s3;
  @    intersect_int_set(s1,intersect_int_set(s2,s3)) == intersect_int_set(intersect_int_set(s1,s2),s3);
  @
  @ axiom intersect_def0:
  @  \forall int_set s; intersect_int_set(empty_int_set,s) == empty_int_set;
  @
  @ axiom intersect_def:
  @  \forall int_set s1, int_set s2, int i;
  @    isin_int_set(s1,i) && isin_int_set(s2,i) <==> isin_int_set(intersect_int_set(s1,s2),i);
  @
  @ axiom size_int_set_def0:
  @  size_int_set(empty_int_set) == 0;
  @
  @ axiom size_int_set_def1:
  @  \forall int_set s, int e;
  @    isin_int_set(s,e) ==> size_int_set(add_int_set(s,e)) == size_int_set(s);
  @
  @ axiom size_int_set_def2:
  @  \forall int_set s, int e;
  @    !isin_int_set(s,e) ==> size_int_set(add_int_set(s,e)) == size_int_set(s)+1;
  @
  @ lemma intset_intersect_prop:
  @     \forall int_set s1,s2;
  @         size_int_set(intersect_int_set(s1,s2)) <= \min(size_int_set(s1),size_int_set(s2));
  @
  @ }
  @*/

/*@ axiomatic IntSet {
  @ logic int_set intset{L}( int* s, integer n) = 
  @    (n == 0) ? empty_int_set : add_int_set(intset{L}(s,n-1), s[n-1]);
  @
  @ lemma intset0{L}:
  @   \forall int* s;
  @     intset{L}(s,0) == empty_int_set;
  @
  @ predicate is_intset{L}( int* s, integer n) = (size_int_set(intset{L}(s,n)) == n);
  @
  @ lemma is_intset0{L}:
  @   \forall int* s;
  @     is_intset{L}(s,0);
  @
  @ lemma is_intset1{L}:
  @   \forall int* s;
  @     is_intset{L}(s,1);
  @
  @ lemma is_intset_new{L}:
  @   \forall int* s, integer n;
  @     is_intset{L}(s,n) && !isin_int_set(intset{L}(s,n),s[n])
  @       ==> is_intset{L}(s,n+1);
  @
  @ lemma is_intset_sub{L}:
  @   \forall int* s, integer n,m;
  @     is_intset(s,n) &&  (0 <= m <= n) ==> is_intset(s,m);
  @
  @ lemma is_intset_ex{L}:
  @   \forall int* s, integer n;
  @     is_intset(s,n) <==> 
  @       (\forall integer i, integer j; 
  @         (0 <= i < n) && (0 <= j < n) && (i != j) ==> (s[i] != s[j]));
  @
  @ lemma isin_int_set_ex{L}:
  @   \forall int* s, integer n, int a;
  @     isin_int_set(intset(s,n),a) <==>
  @       (\exists integer i; (0 <= i < n) && (s[i] == a));
  @
  @ lemma intersect_ex{L1,L2,L3}:
  @   \forall int* s1, int* s2, int* r, integer n1, integer n2, integer k;
  @     (intset{L3}(r,k) == intersect_int_set(intset{L1}(s1,n1),intset{L2}(s2,n2))) <==>
  @       (\forall integer i; (0 <= i < k) ==> 
  @           (\exists integer j1, integer j2; (0 <= j1 < n1) && (0 <= j2 < n2) 
  @             && (\at(r[i],L3) == \at(s1[j1],L1))
  @             && (\at(r[i],L3) == \at(s2[j2],L2))
  @           )
  @       ) &&
  @       (\forall integer j1, integer j2; 
  @         (0 <= j1 < n1) && (0 <= j2 < n2) && (\at(s1[j1],L1) == \at(s2[j2],L2)) ==>
  @           \exists integer i; (0 <= i < k) && (\at(s1[j1],L1) == \at(r[i],L3))
  @       );
  @
  @ lemma intset_intersect_len{L1,L2,L3}:
  @   \forall int* s1, int* s2, int* r, integer n1, integer n2, integer k;
  @     is_intset{L1}(s1,n1) && is_intset{L2}(s2,n2) && is_intset{L3}(r,k) &&
  @     intset{L3}(r,k) == intersect_int_set(intset{L1}(s1,n1),intset{L2}(s2,n2))
  @       ==> (k <= \min(n1,n2));
  @
  @ }
  @*/


/*@ requires \valid(set1+(0..n1-1))
  @       && \valid(set2+(0.. n2-1))
  @       && \valid(result+(0..n1-1))
  @       && \base_addr(set1) != \base_addr(result)
  @       && \base_addr(set2) != \base_addr(result)
  @       && is_intset(set1,n1)
  @       && is_intset(set2,n2);
  @ ensures intset{Here}(result,\result) == intersect_int_set(intset{Pre}(set1,n1),intset{Pre}(set2,n2))
  @      && is_intset(result,\result);
  @*/
unsigned intersect(int* set1, unsigned n1, int* set2, unsigned n2, int* result)
{
unsigned i,j,k;

  k = 0;
  /*@ loop invariant 
    @   (0 <= i <= n1) && 
    @   intset(result,k) == intersect_int_set(intset(set1,i),intset(set2,n2)) &&
    @   is_intset(result,k);
    @ loop variant n1 - i;
    @*/
  for( i = 0; i < n1; i++ )
  {
    /*@ loop invariant 
      @   (0 <= i <  n1) &&
      @   (0 <= j <= n2) &&
      @   intset(result,k) == intersect_int_set(intset(set1,i),intset(set2,n2)) &&
      @   is_intset(result,k) &&
      @   !isin_int_set(intset(set2,j),set1[i]);
      @ loop variant n2 - j;
      @*/
    for( j = 0; j < n2; j++ )
    {
      if (set1[i] == set2[j])
      {
        result[k] = set1[i];
        k++;
        break;
      }
    }
  }
  return k;
}
