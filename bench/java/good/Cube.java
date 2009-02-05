//@+ CheckArithOverflow = no

/*@ lemma distr_right: 
  @   \forall integer x y z; x*(y+z) == (x*y)+(x*z);
  @*/

/*@ lemma distr_left: 
  @   \forall integer x y z; (x+y)*z == (x*z)+(y*z);
  @*/

/*@ lemma distr_right2: 
  @   \forall integer x y z; x*(y-z) == (x*y)-(x*z);
  @*/

/*@ lemma distr_left2: 
  @   \forall integer x y z; (x-y)*z == (x*z)-(y*z);
  @*/

public class Cube {
    /*@ requires x > 0;
      @ ensures \result == x * x * x;
      @*/
  public static int cube(int x) {
    int a = 1;
    int b = 0;
    int c = x;
    int z = 0;
    /*@ loop_invariant 
      @    0 <= c &&
      @    a == 3*(x-c) + 1 &&
      @    b == 3*(x-c)*(x-c) &&
      @    z == (x-c)*(x-c)*(x-c);
      @ loop_variant c;
      @*/
    while (c > 0) {
      z += a + b;
      b += 2*a + 1;
      a += 3;
      c--;
    }
    return z;
  }
}
