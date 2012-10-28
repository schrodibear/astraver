
// int model: unbounded mathematical integers
//@+ CheckArithOverflow = no

/*@ inductive isfact(integer x, integer r) {
  @  case isfact0: isfact(0,1);
  @  case isfactn:
  @   \forall integer n r;
  @     n >= 1 && isfact(n-1,r) ==> isfact(n,r*n);
  @ }
  @*/

public class Fact {

    /*@ requires x >= 0;
      @ ensures isfact(x, \result);
      @*/
    public static int fact(int x) {
        int a = 0, y = 1;
        /*@ loop_invariant 0 <= a <= x && isfact(a,y);
          @ loop_variant x-a;
          @*/
        while (a < x) y = y * ++a;
        return y;
    }

}