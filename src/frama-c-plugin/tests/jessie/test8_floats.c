
/***** polynomial approximation of exp *****/ 
/********** minmax approximation ***********/
/************* Relative error *************/

 

/*@ requires \abs(x) <= 1.0;
  @ ensures \exact(\result) == \exp(\exact(x)) &&  // WRONG !
  @    \relative_error(x) == 0.0 ==> \relative_error(\result) <= 0.04;
  @*/
double my_exp(double x) {
  return 1.027030791 + 1.113889894*x + 0.4693555168*x*x;
}


/* 
Local Variables:
compile-command: "LC_ALL=C make test8_floats"
End:
*/
