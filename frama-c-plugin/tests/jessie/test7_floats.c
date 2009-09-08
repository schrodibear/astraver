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


/* 
Local Variables:
compile-command: "LC_ALL=C make test7_floats"                               
End:
*/
