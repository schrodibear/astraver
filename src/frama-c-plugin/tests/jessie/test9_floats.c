
/***** rationnal approximation of exp *****/ 
/********** minmax approximation ***********/



/*@ requires \abs(x) <= 1.0;
  @ ensures \abs(\result - \exp(x)) <= 0.02097256305;
*/

double monexp(double x) {
  return (1.017021247 + 0.5175411565*x)/(1.0 - 0.4397882839*x);
}


/* 
Local Variables:
compile-command: "LC_ALL=C make test9_floats"                            
End:
*/
