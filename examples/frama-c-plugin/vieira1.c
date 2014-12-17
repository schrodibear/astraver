
// Compilation: frama-c -jessie -jc-opt -separation file.c


/*@ axiomatic Sumone {
  @   // sumone(a,b,n) is true whenever ???
  @   predicate sumone{L1,L2}(integer k1,int *a1,int *b1, integer k2,int *a2,int *b2, integer n);
  @ axiom sumone_start{L} :
  @   \forall integer k1, k2; \forall int *a, *b;
  @			  \forall integer n, i;
  @        k1==k2 ==> sumone{L,L}(k1,a,b,k2,a,b,n);
  @ axiom sumone_inv{L1,L2,L3} :
  @    \forall integer k1, k2, k3, n; \forall int *a1, *b1, *a2, *b2, *a3, *b3;
  @     sumone{L1,L2}(k1,a1,b1,k2,a2,b2,n)
  @	// && k3 == k2 + 1
  @	// && \at(b3[k2],L3) == \at(a3[k2],L3) + 1
  @     // && (\forall integer l; 0<=l<n ==> \at(a3[l],L3)== \at(a2[l],L2))
  @	// && (\forall integer l; 0<=l<n && k2!=l ==> \at(b3[l],L3)== \at(b2[l],L2))
  @	==> sumone{L1,L3}(k1,a1,b1,k3,b3,b3,n);
  @ axiom sumone_end{L1,L2} :
  @    \forall int *a1, *b1, *a2, *b2, integer k2, n;
  @     sumone{L1,L2}((int)0,a1,b1,k2,a2,b2,n) &&
  @     k2 == n
  @	==>
  @        (\forall integer l; 0<=l<n ==> \at(b2[l],L2) == \at(a2[l],L2) + 1)
  @     && (\forall integer l; 0<=l<n ==> \at(a2[l],L2)== \at(a1[l],L1));
  @ }
  @*/


 /*int a[10];
 int b[10];
 int n = 10;
 */

/*@ requires
  @   \valid(a+(0..n)) &&  \valid(b+(0..n)) &&
  @	  n>0 && 0<=i<n;
  @ ensures b[i] == a[i]+ 1;
  @*/
void func(int i,int a[], int b[],int n){
   int k;

  /*@ loop invariant
    @	 sumone{Pre,Here}((int)0,a,b,k,a,b,n) && 0<=k<=n;
    @ loop variant
    @	(n-k);
    @*/
  for(k=0;k<n;k++) {
    b[k] = a[k] + 1;
  }
    /*@ ghost goto L;
      @*/
    /*@ ghost L:
      @*/


   /*@ loop invariant
     @ 	(\forall int l; 0<=l<n ==> \at(b[l],L) == \at(b[l],Here)) &&
     @	0<=k<=n;
     @*/
    for(k=0;k<n;k++) {
      a[k] = a[k];
    }


}
