/*

  This was inspired by this article:

    Franck Butelle, Florent Hivert, Micaela Mayero, and Frédéric
    Toumazet. Formal Proof of SCHUR Conjugate Function. In Proceedings
    of Calculemus 2010, pages 158-171. Springer-Verlag LNAI, 2010.

  and an improvement made in Why3 (http://why3.lri.fr) by
  Jean-Christophe Filliatre

  Original C code from SCHUR

  Note that arrays are one-based
  (that code was translated from Pascal code where arrays were one-based)

*/

#define MAX 100

/*@ predicate is_partition(int *a) =
    // elements ranges between 0 and MAX-1
    (\forall integer i; 1 <= i < MAX ==> 0 <= a[i] < MAX-1) &&
    // sorted in non-increasing order 
    (\forall integer i,j; 1 <= i <= j < MAX ==> a[i] >= a[j]) &&
    // at least one 0 sentinel
    a[MAX-1] == 0 ;

  predicate numofgt (int *a, integer n, integer v) =
    // values in a[1..n] are >= v, and a[n+1] < v
    0 <= n < MAX-1 &&
    (\forall integer j; 1 <= j <= n ==> v <= a[j]) &&
    v > a[n+1] ;

  predicate is_conjugate (int *a, int *b) =
    MAX > a[1] &&
    \forall integer j; 1 <= j < MAX ==> numofgt(a,b[j],j);

*/

/*@ requires \valid(A + (0 .. MAX-1));
  @ requires \valid(B + (0 .. MAX-1));
  @ // requires \forall integer i; 1 <= i < MAX ==> 1 <= A[i] < MAX-1;
  @ requires \forall integer k; 1 <= k < MAX ==> B[k] == 0;
  @ requires is_partition(A);
  @ assigns B[..];
  @ ensures is_conjugate(A,B);
  @*/
void conjgte (int A[MAX], int B[MAX]) {
  int i, partc = 1, edge = 0;
  /*@ loop invariant 1 <= partc < MAX;
    @ loop invariant \forall integer j;
    @   A[partc] < j <= A[1] ==> numofgt(A,B[j],j);
    @ loop invariant \forall integer j;
    @   A[1] < j < MAX ==> B[j] == 0;
    @ loop variant MAX - partc;
    @*/
  while (A[partc] != 0) 
    Start: {
    edge = A[partc];
    /*@ loop invariant \at(partc,Start) <= partc < MAX-1;
      @ loop invariant \forall integer j; 
      @    \at(partc,Start) <= j < partc ==> A[j] == edge;
      @ loop variant MAX - partc;
      @*/
    do
      partc = partc + 1;
    while (A[partc] == edge);
    /*@ loop invariant 1 <= i;
      @ loop invariant \forall integer j;
      @   edge < j < MAX ==> B[j] == \at(B[j],Start);
      @ loop invariant \forall integer j;
      @   A[partc] < j < i ==> B[j] == partc-1;
      @ loop variant edge-i;
      @*/
    for (i = A[partc] + 1; i <= edge; i++)
      B[i] = partc - 1;
  }
}

