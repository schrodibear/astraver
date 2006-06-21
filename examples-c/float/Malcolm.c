/*@ ensures \result == 2 ^^ (53)
  @*/

double malcolm1() {
  double A;
  A=2;
 
  while (A != (A+1)) {
    A*=2;
  }
  return A;
}
