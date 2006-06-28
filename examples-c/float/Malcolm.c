/*@ logic int my_log(real s) */

/*@ ensures \result == 2  */

double malcolm1() {
  double A;
  A=2;
  /*@ assert my_log(A)==1 */

  return A;
}
