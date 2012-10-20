/*
COST Verification Competition. vladimir@cost-ic0701.org

Challenge 1: Maximum in an array

Given: A non-empty integer array a.

Verify that the index returned by the method max() given below points to
an element maximal in the array.

*/

/*@ axiomatic integer_max {
  @   logic integer max(integer x, integer y);
  @   axiom max_is_ge : \forall integer x y; max(x,y) >= x && max(x,y) >= y;
  @   axiom max_is_some : \forall integer x y; max(x,y) == x || max(x,y) == y;
  @ }
  @*/

public class ArrayMax {


    /*@ requires a.length > 0;
      @ ensures 0 <= \result < a.length &&
      @   \forall integer i; 0 <= i < a.length ==> a[i] <= a[\result];
      @*/
    public static int max(int[] a) {
        int x = 0;
        int y = a.length-1;
        /*@ loop_invariant 0 <= x <= y < a.length &&
          @      \forall integer i;
          @         0 <= i < x || y < i < a.length ==>
          @         a[i] <= max(a[x],a[y]);
          @ loop_variant y - x;
          @*/
        while (x != y) {
            if (a[x] <= a[y]) x++;
                else y--;
        }
        return x;
    }

}

/*
Local Variables:
compile-command: "make ArrayMax.why3ide"
End:
*/

