


/*@ axiomatic T {
  @    predicate p(real x);
  @    axiom a: \forall real x; x >= 0 ==> p(x);
  @ }
  @*/


/*@ ensures p(\result);
  @*/
double f() {
  //@ returns \result == 1.0;
  return 1.0;
}


