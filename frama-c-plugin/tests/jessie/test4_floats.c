/* run.config
 */

#pragma JessieFloatModel(strict)

/*@ requires \abs(x) <= 0x2.p-3;
  @ ensures
  @    \model(\result) == \exp(\model(x))
  @ && (\round_error(x) == 0.0 ==> \round_error(\result)<= 0x2.p-52
  @ && \total_error(\result) <= \total_error(x) + 0x2.p-51);
  @ */

double monexp(double x) {
  //@ assert round2: (double)2.0 == 2.0;
  double y=1.0+x*(1.0+x/2.0);
  //*@ \set_model y exp(\model(x)); */
  return y;
}


/* 
Local Variables:
compile-command: "LC_ALL=C make test4_floats"                               
End:
*/
