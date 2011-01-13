/* Frama-C BTS 0362

read effects were computed wrong

Status: Closed 


*/

/*@ axiomatic s_axioms {
    // compute the sum a[0]+...+a[i]:
    logic integer s{L}(int* a,integer i);

    axiom s_base{L}: \forall int* a, integer i;
	i < 0 ==> s{L}(a,i) == 0;

    axiom s_step{L}: \forall int* a, integer i;
	i >= 0 ==> s{L}(a,i) == s{L}(a,i-1) + \at(a,L)[i];
} */

//@ requires \valid_range(b,0,8);
void ftest(int b[9])
{
M:
    b[4] = 5;
    //@ assert \forall int *c; s{Here}(c,8) == s{M}(c,8);
    //@ assert                 s{Here}(b,8) == s{M}(b,8);
}


/*
Local Variables:
compile-command: "make bts0362"
End:
*/

