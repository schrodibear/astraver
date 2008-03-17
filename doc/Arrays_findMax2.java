
/*@ predicate is_max(int[] t,integer i,integer l) {
  @   0 <= i < l &&
  @      \forall integer j; 0 <= j < l ==> t[j] <= t[i] }
  @*/

public class Arrays {

    /*@ requires t != null && t.length >= 1;
      @ ensures is_max(t,\result,t.length);
      @*/
    public static int findMax2(int[] t) {
        int m = t[0];
        int r = 0;
        /*@ loop_invariant 
          @   1 <= i <= t.length && m == t[r] && is_max(t,r,i) ;
          @ decreases t.length-i;
          @*/
        for (int i=1; i < t.length; i++) {
            if (t[i] > m) {
                r = i; 
                m = t[i];
            }
        }
        return r;
    }

}