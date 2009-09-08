
#pragma JessieFloatModel(strict)

/*@ requires \abs(x) <= 0x1p-5; 
  @ ensures \abs(\result - \cos(x)) <= 0x1p-23;  
  @*/
float moncos(float x) {
  //@ assert \abs(1.0 - x*x*0.5 - \cos(x)) <= 0x1p-24;
  return 1.0f - x * x * 0.5f;
}

/*@ requires \abs(x) <= 0x1p-5 
  @     && \round_error(x) == 0.0; 
  @ ensures \abs(\result - \cos(x)) <= 0x1p-23;  
  @*/
float cosine2(float x) {
  float r = 1.0f - x * x * 0.5f;
  //@ assert \abs(\exact(r) - \cos(x)) <= 0x1p-24;
  return r;
}

/*@ lemma abs_triangle: \forall real x,y,z;
  @            \abs(x-y) <= \abs(x-z)+\abs(z-y);
  @*/

/*@ requires \abs(\exact(x)) <= 0x1p-5 
  @     && \round_error(x) <= 0x1p-20;  
  @ ensures \abs(\exact(\result) - \cos(\exact(x))) <= 0x1p-24
  @     && \round_error(\result) <= \round_error(x) + 0x0.3p-20;  
  @*/
float cosine1a(float x) {
  float r = 1.0f - x * x * 0.5f;
  //@ assert \abs(x) <= 0x1.0002p-5; // by SMT provers and lemma abs_triangle
  //@ assert \abs(1.0 - \exact(x)*\exact(x)*0.5 - \cos(\exact(x))) <= 0x1p-24;  // by interval
  //@ assert \abs(1.0 - x*x*0.5 - \cos(x)) <= 0x1p-24;                          // by interval
  //@ assert \abs(r - \cos(x)) <= 0x1p-23;                          // by gappa
  /*@ assert \round_error(r) <= \abs(r - \cos(x)) + 
    @                           \abs(\cos(x)-\cos(\exact(x))) + 
    @                           \abs(\cos(\exact(x)) - \exact(r));   // by SMT provers and lemmas above
    @*/
  return r;
}

/*@ requires \abs(x) <= 0.07 ; 
  @ ensures \abs(\result - \cos(x)) <= 0x1p-20;  
  @*/
float cosine1b(float x) {
  //@ assert \abs(1.0 - x*x*0.5 - \cos(x)) <= 0x0.Fp-20;
  return 1.0f - x * x * 0.5f;
}





/* 
Local Variables:
compile-command: "LC_ALL=C make test1_floats"
End:
*/


