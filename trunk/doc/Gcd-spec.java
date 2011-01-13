
/*@ predicate divides(integer x, integer y) {
  @   \exists integer q; y == q*x
  @ }
  @*/

/*@ predicate isGcd(integer a, integer b, integer d) {
  @   divides(d,a) && divides(d,b) && 
  @     \forall integer z;
  @     divides(z,a) && divides(z,b) ==> divides(z,d) }
  @*/

class Gcd {

    /*@ requires x >= 0 && y >= 0;
      @ behavior resultIsGcd: 
      @   ensures isGcd(x,y,\result) ;
      @ behavior bezoutProperty:
      @   ensures \exists integer a,b; a*x+b*y == \result;
      @*/
    static int gcd(int x, int y);

}
