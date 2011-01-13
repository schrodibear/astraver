

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

#include <stdlib.h>

/*@ requires size == sizeof(X);
  @ ensures Permut{Old,Here}<X>(base,0,nmemb-1); 
  @*/
void qsort
  /*@ <X> */ 
(void *base , 
   size_t nmemb, 
   size_t size,
   int(*compar)(const void *, const void *));












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

int main() { 
  struct date b[] = { {1,1,2010} , { 2,2, 2009}, {3,3,2010}};
  qsort
    /*@ <struct date> */
    (b,3,sizeof(struct date),compare_for_qsort);
  //@ assert(b[0].year <= b[1].year);
  return 0;
}




/*
Local Variables:
compile-command: "make qsort-permut"
End:
*/
