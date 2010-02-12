/* run.config
 */

#pragma JessieFloatModel(strict)


/*@ ensures \result == (double)(\sqrt(x));
  @*/
double sqrt(double x);


/*@ ensures \result == 0x1p-52;
  @*/
double poly() {
  double x = sqrt(2.0)/2.0;
  return 2.0*x*x-1.0;
}

/* 
Local Variables:
compile-command: "LC_ALL=C make test2_floats"
End:
*/


