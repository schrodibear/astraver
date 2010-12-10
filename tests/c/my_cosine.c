// does not work: RUN GAPPA: will ask regtests to run Gappa on this program
// RUNCOQ: for the first VC


/*@ lemma method_error: \forall real x;
  @     \abs(x) <= 0x1p-5 ==> \abs(1.0 - x*x*0.5 - \cos(x)) <= 0x1p-24;
  @*/

/*@ requires \abs(x) <= 0x1p-5;
  @ ensures \abs(\result - \cos(x)) <= 0x1p-23;
  @*/
float my_cos1(float x) {
  //@ assert \abs(1.0 - x*x*0.5 - \cos(x)) <= 0x1p-24;
  return 1.0f - x * x * 0.5f;
}

/*@ requires \abs(x) <= 0x1p-5
  @     && \round_error(x) == 0.0;
  @ ensures \abs(\result - \cos(x)) <= 0x1p-23;
  @*/
float my_cos2(float x) {
  float r = 1.0f - x * x * 0.5f;
  //@ assert \abs(\exact(r) - \cos(x)) <= 0x1p-24;
  return r;
}


/*@ requires \abs(\exact(x)) <= 0x1p-5
  @     && \round_error(x) <= 0x1p-20;
  @ ensures \abs(\exact(\result) - \cos(\exact(x))) <= 0x1p-24
  @     && \round_error(\result) <= \round_error(x) + 0x3p-24;
  @*/
float my_cos3(float x) {
  float r = 1.0f - x * x * 0.5f;
  //@ assert \abs(\exact(r) - \cos(\exact(x))) <= 0x1p-24;  // by interval
  return r;
}

/*@ requires \abs(x) <= 0.07 ;
  @ ensures \abs(\result - \cos(x)) <= 0x1p-20;
  @*/
float my_cos4(float x) {
  //@ assert \abs(1.0 - x*x*0.5 - \cos(x)) <= 0x0.Fp-20;
  return 1.0f - x * x * 0.5f;
}


/*
Local Variables:
compile-command: "frama-c -jessie my_cosine.c"
End:
*/


