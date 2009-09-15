#pragma JessieFloatModel(strict)


/***** polynomial approximation of exp *****/ 
/********** minmax approximation ***********/
/************* Remez algorithm *************/


/*@ requires \abs(x) <= 1.0;
  @ ensures \abs(\result - \exp(x)) <= 0x1p-4; 
  @ */

double monexp(double x) {
  /*@ assert \abs(0.9890365552 + 1.130258690*x + 0.5540440796*x*x - \exp(x)) 
                  <= 0x0.FFFFp-4;
    @*/
  return 0.9890365552 + 1.130258690*x + 0.5540440796*x*x;
}


/*@ lemma abs_triangle: \forall real x,y,z;
  @            \abs(x-y) <= \abs(x-z)+\abs(z-y);
  @*/

/*@ requires \abs(\exact(x)) <= 1.0 
  @     && \round_error(x) <= 0x1p-20;  
  @ ensures \abs(\exact(\result) - \exp(\exact(x))) <= 0x1p-4
  @     && \round_error(\result) <= \round_error(x) + 0x0.3p-20;  
  @*/
double exp1(double x) {
  float r = 0.9890365552 + 1.130258690*x + 0.5540440796*x*x;
  //@ assert \abs(x) <= 0x1.00001p0; // by SMT provers and lemma abs_triangle
  /*@ assert \abs(\exact(r) - \exp(\exact(x))) <= 0x0.FFFFp-4;  // by interval
    @*/
  /*@ assert \abs(0.9890365552 + 1.130258690*x + 0.5540440796*x*x - \exp(x)) 
    @ <= 0x1p-4;                          // by interval
    @*/
  //@ assert \abs(r - \exp(x)) <= 0x1p-4;                          // by gappa
  /*@ assert \round_error(r) <= \abs(r - \exp(x)) + 
    @                           \abs(\exp(x)-\exp(\exact(x))) + 
    @                           \abs(\exp(\exact(x)) - \exact(r));   // by SMT provers and lemmas above
    @*/
  return r;
}


/* 
Local Variables:
compile-command: "LC_ALL=C make test7_floats"                               
End:
*/
