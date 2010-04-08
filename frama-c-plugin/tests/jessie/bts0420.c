
/* Frama-C BTS 0420

Status: fixed

*/



#pragma JessieIntegerModel(math)

//@ predicate e{L}(int* a,int* b) = ( a[0] == b[0] );

/*@ axiomatic ax1 {
    predicate p{L1,L2}(int* a);
    axiom ax2{L1,L2}: \forall int* a, int* b;
	e{L1}(a,b) && p{L1,L2}(a) && e{L2}(a,b) ==> p{L1,L2}(b);
    }
*/

// remove '@' to make assertion in line 24 unprovable:
/* @ lemma lm1{L1,L2}: \forall int* a, int* b;
	e{L1}(a,b) && p{L1,L2}(a) && e{L2}(a,b) ==> p{L1,L2}(b);
*/

//@ requires \valid_range(a,0,9) && \valid_range(b,0,9);
void ftest(int *a,int *b) {
L1:
    // ensure mem state at L2 cant be expressed in terms of that at L1:
  //@ loop invariant 0 <= i <= 9; loop variant 9-i;
    for (int i=0; i<9; ++i) {
	a[0] += b[i];
	b[0] += a[i];
    }
L2:
    //@ assert e{L1}(a,b) && p{L1,L2}(a) && e{L2}(a,b) ==> p{L1,L2}(b);
    return;
}
