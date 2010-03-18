

// The polymorphic permutation predicate 

/*@

predicate Swap{L1,L2}<X>(X *a, integer i, integer j) =
 \at(a[i],L1) == \at(a[j],L2) && \at(a[j],L1) == \at(a[i],L2) &&
 \forall integer k; k != i && k != j ==> \at(a[k],L1) == \at(a[k],L2);

inductive Permut{L1,L2}<X>(X *a, integer l, integer h){
 case Permut_refl{L}: \forall X *a, integer l,h; 
   Permut{L,L}(a, l, h);
 case Permut_sym{L1,L2}: \forall X *a, integer l,h; 
   Permut{L1,L2}(a, l, h) ==> Permut{L2,L1}(a, l, h);
 case Permut_trans{L1,L2,L3}: \forall X *a, integer l,h; 
   Permut{L1,L2}(a, l, h) && 
     Permut{L2,L3}(a, l, h) ==> Permut{L1,L3}(a, l, h);
 case Permut_swap{L1,L2}: \forall X *a, integer l,h,i,j; 
   l <= i <= h && l <= j <= h && 
      Swap{L1,L2}(a, i, j) ==> Permut{L1,L2}(a, l, h);
}

*/





// The theory of some ordering on X

/*@ 

theory ComparatorTheory<X> { 
  predicate eq{L}(X x, X y);  
  axiom eq_ref{L}: \forall X a; eq{L}(a,a);
  axiom eq_sym{L}: \forall X a,b; eq{L}(a, b) ==> eq{L}(b,a);
  axiom eq_trans{L}: \forall X a1,a2,a3; 
    eq{L}(a1, a2) && eq{L}(a2,a3) ==> eq{L}(a1,a3);

  predicate lt{L}(X x, X y);  
  axiom lt_irref{L}: \forall X a; ! lt{L}(a,a);
  axiom lt_antisym{L}: \forall X a1,a2; !(lt{L}(a1,a2) && lt{L}(a2,a1))
  axiom lt_trans{L}: \forall X a1,a2,a3; 
    lt{L}(a1,a2) && lt{L}(a2,a3) ==> lt{L}(a1,a3);
  axiom lt_totality{L}: \forall X a1,a2; 
    eq{L}(a1,a2) || lt{L}(a1,a2) || lt{L}(a2,a1); 

  predicate leq{L}(X x, X y) = eq{L}(x,y) || lt{L}(x,y); 

  predicate sorted{L}(X *a, integer l, integer h) =
    \forall integer i; l <= i < h ==> leq{L}(\at(a[i],L),\at(a[i+1],L));

}


*/



#include <stdlib.h>

/*@ requires size == sizeof(X);
  @ ensures Permut{Old,Here}(base,0,nmemb-1); 
  @ ensures th.sorted(base,0,nmemb-1); 
  @*/
void qsort
  /*@ <X> < th instantiating ComparatorTheory<X> > */ 
  (void* base /* as X* */, 
   size_t nmemb, 
   size_t size,
   int(*compar)(const void *, const void *)
   /* as
      int(*compar)(const X *x, const Y *y);
        ensures (th.lt(x,y) <==> \result < 0) &&
           (th.eq(x,y) <==> \result == 0) &&
              (th.lt(y,x) <==> \result > 0);    
   */
   );








/**** client code *************/



struct date {
  int day;
  int month;
  int year;
};


int compare_by_year(const struct date *x, const struct date *y) {
  if (x->year < y->year) return -1;
  if (x->year == y->year) return 0;
  return 1;
}


int compare_for_qsort(const void *x, const void *y) {
  return compare_by_year((struct date *)x,(struct date *)y);
}

/*@
theory ByYear instantiates ComparatorTheory<struct date *> {
  predicate eq{L}(struct date *x, struct date *y) = 
        \at(x->year == y->year, L);
  predicate lt{L}(struct date *x, struct date *y) = 
        \at(x->year < y->year, L);
}
*/

int main() { 
  struct date b[] = { {1,1,2010} , { 2,2, 2009}, {3,3,2010}};
  qsort
    /*@ <struct date> <ByYear> */
    (b,3,sizeof(struct date),compare_for_qsort);
  //@ assert(b[0].year <= b[1].year);
  return 0;
}




/*
Local Variables:
compile-command: "make qsort-annotated"
End:
*/
