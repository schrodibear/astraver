
union U {
  int i;
  struct { int i1 : 15; int i2 : 17; } si;
};

//@ requires \valid(x);
void zero(union U* x) {
  x->i = 0;
  //@ assert x->si.i1 == 0;
  //@ assert x->si.i2 == 0;
}

/*
File "jc/jc_effect.ml", line 525, characters 14-14:
Uncaught exception: File "jc/jc_effect.ml", line 525, characters 14-20: Assertion failed
*/
