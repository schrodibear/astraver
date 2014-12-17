/* Frama-C BTS 0341

Status: open

yields:

File "jc/jc_interp.ml", line 1630, characters 13-13:
Uncaught exception: File "jc/jc_interp.ml", line 1630, characters 13-19: Assertion failed

*/

#pragma JessieIntegerModel(math)

union U {
  int i;
  struct { short s1; short s2; } s;
};

//@ requires \valid(x);
void zero(union U* x) {
  x->i = 0;
  //@ assert x->s.s1 == 0;
  //@ assert x->s.s2 == 0;
}


/*
Local Variables:
compile-command: "make bts0341"
End:
*/

