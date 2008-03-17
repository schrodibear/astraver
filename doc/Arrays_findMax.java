
//@+ CheckArithOverflow = no

public class Arrays {

    /*@ requires t != null && t.length >= 1;
      @ ensures 
      @   0 <= \result < t.length && 
      @   \forall integer i; 0 <= i < t.length ==> t[i] <= t[\result];
      @*/
    public static int findMax(int[] t);
	
}
