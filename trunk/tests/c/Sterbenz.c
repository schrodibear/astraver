// RUNCOQ: will ask regtests to check Coq proofs of this program

/*@ requires  y / 2.0 <= x <= 2.0 * y;
  @ ensures   \result == x - y;
  @*/
float Sterbenz(float x, float y) {
  //@ assert 0.0 <= y;
  //@ assert 0.0 <= x;
  return x-y;
}


/*
Local Variables:
compile-command: "frama-c -jessie -jessie-atp coq Sterbenz.c"
End:
*/
