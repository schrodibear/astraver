/*@ requires n > 0; 
    requires \valid(p+ (0..n-1));
    assigns \nothing;
    ensures \forall integer i; 0 <= i <= n-1 ==> \result >= p[i]; 
    ensures \exists integer e; 0 <= e <= n-1 &&  \result == p[e]; 
 */ 
int max_seq(int* p, int n) {

  int res = *p; 
  int i   = 0;

  //@ ghost int e = 0;
  /*@ loop invariant 0 <= i <= n;
    @ loop invariant 0 <= e <= n-1;
    @ loop invariant p == \at(p,Pre)+i;
    @ loop invariant \forall integer j; 0 <= j < i ==> res >= *(\at(p,Pre)+j);
    @ loop invariant \valid(\at(p,Pre)+e) && \at(p,Pre)[e] == res;
    @ loop variant n-i;
    @*/
  for(i = 0; i < n; i++) { 
    if (res < *p) { 
       res = *p; 
       //@ ghost e = i;
    }
    p++; 
  } 
  return res; 
} 
