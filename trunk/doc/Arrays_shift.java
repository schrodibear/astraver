public class Arrays {

    /*@ requires t != null;
      @ ensures 
      @   \forall integer i; 0 < i < t.length ==> t[i] == \old(t[i-1]);
      @*/
    public static void shift(int[] t) {
	/*@ loop_invariant 
	  @   j < t.length &&
	  @   (\forall integer i; 0 <= i <= j ==> t[i] == \at(t[i],Pre)) &&
	  @   (\forall integer i; 
	  @         j < i < t.length ==> t[i] == \at(t[i-1],Pre));
	  @ decreases j;
	  @*/
	for (int j=t.length-1 ; j > 0 ; j--) {
	    t[j] = t[j-1];
	}
    }

}
