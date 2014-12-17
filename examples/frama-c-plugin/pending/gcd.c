/*@ predicate divides(int x, int y) {
  @   \exists int q; y == q*x
  @ }
  @*/

/*@ axiom div_mod_property:
  @  \forall int x, int y;
  @    x >=0 && y > 0 ==> x == y*(x/y) + (x%y) ;
  @*/

/*@ requires x >= 0 && y >= 0;
  @ behavior divides_both:
  @   ensures divides(\result,x) && divides(\result,y);
  @ behavior is_greatest_divisor:
  @   ensures \forall int z;
  @     z>0 && divides(z,x) && divides(z,y) ==> z>=\result;
  @ behavior bezout_property:
  @   ensures \exists int a, int b; a*x+b*y == \result;
  @*/
int gcd(int x, int y) {
  //@ ghost int a = 1;
  //@ ghost int b = 0;
  //@ ghost int c = 0;
  //@ ghost int d = 1;
  /*@ loop invariant
    @    a*\old(x)+b*\old(y) == x &&
    @    c*\old(x)+d*\old(y) == y ;
    @ loop variant y;
    @*/
  while (y > 0) {
    int r = x % y;
    //@ ghost int q = x / y;
    x = y;
    y = r;
    //@ ghost int ta = a;
    //@ ghost int tb = b;
    //@ ghost a = c;
    //@ ghost b = d;
    //@ ghost c = ta - c * q;
    //@ ghost d = tb - d * q;
  }
  return x;
}

/* 
Local Variables:
compile-command: "LC_ALL=C make gcd"
End:
*/
