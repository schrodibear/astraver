


public class negate {

    /*@ requires t != null;
      @ assigns t[0..t.length-1];
      @ ensures \forall integer k; 0 <= k < t.length ==> t[k] == -\old(t[k]);
      @*/
    static void negate(int t[]) {
	int i = 0;
	/*@ loop_invariant 
	  @   0 <= i <= t.length && 
	  @   (\forall integer k; 0 <= k < i ==> t[k] == -\at(t[k],Pre)) ;
	  @ loop_assigns t[0..i-1];
	  @ loop_variant t.length-i; 
	  @*/
	while (i < t.length) {
	    t[i] = -t[i];
	    i++;
	}
	
    }

}
