/*@

predicate f{L1,L2}(int *t1,int *t2) =
  \forall integer i,j; \at(t1[i],L1) == \at(t2[j],L2);

predicate g{L1,L2}(int *t) =
  \forall integer i,j; \at(t[i],L1) == \at(t[j],L2);

*/

/*@ ensures f{Here,Old}(t,t);
  @ ensures g{Here,Old}(t);
  @*/
void f(int t[]) {
  return;
}
