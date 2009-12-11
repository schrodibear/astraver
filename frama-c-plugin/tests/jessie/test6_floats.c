/* run.config
   DONTRUN: bug typing : "cannot cast to logic type"
 */

#pragma JessieFloatModel(strict)


/*@ axiomatic KillingProp {
  @    predicate my_killing_prop(double uc, double up, integer n); 
  @ }
  @*/

/*@ requires 2 <= N <= 0x1p26 && 
  @      \exact(u0)==u0 && \exact(u1)==u1 &&
  @      \forall integer k; 0 <= k <= N ==> \abs(u0+k*(u1-u0)) <= 1;
  @ ensures  \exact(\result)== u0+N*(u1-u0) &&
  @          \round_error(\result) <= (N)*(N+1)/2.0* 0x1p-53;
  @*/
double comput_seq(double u0, double u1, int N) {
  int i;
  double uprev, ucur,tmp;
  uprev=u0;
  ucur=u1;

  /*@ loop invariant 2 <= i <= N+1 && 
    @   \exact(ucur) == u0+(i-1)*(u1-u0) &&
    @   \exact(uprev)== u0+(i-2)*(u1-u0) &&
    @   my_killing_prop(ucur,uprev,i-2); 
    @ loop variant N-i; 
    @*/ 
  for (i=2; i<=N; i++) {
    tmp=2*ucur;
    /*@ assert tmp==2*ucur; */
    tmp-=uprev;
    uprev=ucur;
    ucur=tmp;
  }
  return ucur;
}



/* 
Local Variables:
compile-command: "LC_ALL=C make test6_floats"
End:
*/
