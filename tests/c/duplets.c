/*
COST Verification Competition. vladimir@cost-ic0701.org

Challenge 3: Two equal elements

Given: An integer array a of length n+2 with n>=2. It is known that at
least two values stored in the array appear twice (i.e., there are at
least two duplets).

Implement and verify a program finding such two values.

You may assume that the array contains values between 0 and n-1.
*/

#define NULL (void*)0

/* equality between an integer and a possibly null int* */
/*@ predicate eq_opt{L}(integer x, int *o) =
  @   o != \null && x == *o ;
  @*/

/* A duplet in array a is a pair of indexes (i,j) in the bounds of array
   a such that a[i] = a[j] */
/*@ predicate is_duplet{L}(int *a, integer len, integer i, integer j) =
  @    0 <= i < j < len && a[i] == a[j];
  @*/

/* duplet(a) returns the indexes (i,j) of a duplet in a.
 * moreover, if except is not null, the value of this duplet must
 * be different from it.
 */
/*@ requires 2 <= len &&
  @   \valid_range(a,0,len-1) && \valid(pi) && \valid(pj) &&
  @   ( except == \null || \valid(except)) &&
  @   \exists integer i,j;
  @     is_duplet(a,len,i,j) && ! eq_opt(a[i],except) ;
  @ assigns *pi,*pj;
  @ ensures
  @   is_duplet(a,len,*pi,*pj) &&
  @   ! eq_opt(a[*pi],except);
  @*/
void duplet(int *a, int len, int *except, int *pi, int *pj) {
  /*@ loop invariant 0 <= i <= len-1 &&
    @  \forall integer k,l; 0 <= k < i && k < l < len ==>
    @    ! eq_opt(a[k],except) ==> ! is_duplet(a,len,k,l);
    @ loop variant len - i;
    @*/
  for(int i=0; i <= len - 2; i++) {
    int v = a[i];
    if (except == NULL || *except != v) {
      /*@ loop invariant i+1 <= j <= len &&
        @   \forall integer l; i < l < j ==> ! is_duplet(a,len,i,l);
        @ loop variant len - j;
        @*/
      for (int j=i+1; j < len; j++) {
        if (a[j] == v) {
          *pi = i; *pj = j; return;
        }
      }
    }
  }
  // assert \forall integer i j; ! is_duplet(a,i,j);
  //@ assert \false;
}



/*@ requires 4 <= len && 
  @   \valid_range(a,0,len-1) && \valid(pi) && \valid(pj) &&
  @   \valid(pk) && \valid(pl) &&
  @   \exists integer i,j,k,l;
  @     is_duplet(a,len,i,j) && is_duplet(a,len,k,l) && a[i] != a[k];
  @ assigns *pi,*pj,*pk,*pl;
  @ ensures is_duplet(a,len,*pi,*pj) &&
  @   is_duplet(a,len,*pk,*pl) &&
  @   a[*pi] != a[*pk];
  @*/
void duplets(int a[], int len, int *pi, int *pj, int *pk, int *pl) {
  duplet(a,len,NULL,pi,pj);
  duplet(a,len,&a[*pi],pk,pl);
}


/*
Local Variables:
compile-command: "make duplets.why3ide"
End:
*/

