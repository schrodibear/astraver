/*@ predicate divides(int x, int y) {
  @   \exists int q; y == q*x
  @ }
  @*/

/*@ axiom div_mod_property:
  @  \forall int x; \forall int y; 
  @    x >=0 && y > 0 => x == y*(x/y) + (x%y) 
  @*/

/*@ requires x >= 0 && y >= 0
  @ ensures 
  @  (divides_both::
  @    divides(\result,x) && divides(\result,y)) &&
  @  (is_greatest_divisor::
  @    \forall int z;
  @      z>0 && divides(z,x) && divides(z,y) => z>=\result) && 
  @  (bezout_property::
  @    \exists int a; \exists int b; a*x+b*y == \result)
  @*/
int gcd(int x, int y) {
  //@ ghost int a = 1
  //@ ghost int b = 0
  //@ ghost int c = 0
  //@ ghost int d = 1
  /*@ invariant 
    @    a*\old(x)+b*\old(y)==x && 
    @    c*\old(x)+d*\old(y)==y 
    @ variant y
    @*/
  while (y > 0) {
    int r = x % y;
    //@ ghost int q = x / y
    x = y;
    y = r;
    //@ ghost int ta = a;
    //@ ghost int tb = b;
    //@ set a = c; 
    //@ set b = d;
    //@ set c = ta - c * q;
    //@ set d = tb - d * q;
  }
  return x;
}

