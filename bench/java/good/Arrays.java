
/*@ predicate is_max(int[] t,int i,int l) {
  @   t != null && 0<=i && i < l && l <= t.length &&
  @   (\forall integer j; 0 <= j && j < l ==> t[j] <= t[i])
  @ }
  @*/

public class Arrays {

    /*@ requires t != null && 1 <= t.length && t.length <= 32767;
      @ behavior max_found:
      @   ensures 
      @      0 <= \result && \result < t.length && 
      @      (\forall integer i; 
      @           0 <= i && i < t.length ==> t[i] <= t[\result]);
      @*/
    public static short findMax(int[] t) {
	int m = t[0];
	short r = 0;
        /*@ loop_invariant 
          @   1 <= i && i <= t.length && 0 <= r && r < t.length &&
          @   m == t[r] && (\forall integer j; 0<=j && j<i ==> t[j]<=m);
          @ decreases t.length-i;
          @*/
	for (short i=1; i < t.length; i++) {
	    if (t[i] > m) {
		r = i; 
		m = t[i];
	    }
	}
	return r;
    }

    /*@ requires t != null && t.length >= 1;
      @ behavior max_found:
      @  ensures 
      @      0 <= \result && \result < t.length && 
      @      is_max(t,\result,t.length) ;
      @*/
    public static int findMax2(int[] t) {
	int m = t[0];
	int r = 0; 
	/*@ loop_invariant 
	  @   1 <= i && i <= t.length && 0 <= r && r < t.length &&
          @   m == t[r] && is_max(t,r,i) ;
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


    /*@ requires t != null ;
      @ behavior shifted:
      @   ensures 
      @    \forall int i; 0 < i && i < t.length ==> t[i] == \old(t[i-1]);
      @*/
    public static void arrayShift(int[] t) {
	/*@ loop_invariant 
	  @   j < t.length &&
	  @   (t.length > 0 ==>
	  @     (0 <= j && 
          @     (\forall int i; 0 <= i && i <= j ==> t[i] == \old(t[i])) &&
          @     (\forall int i; j < i && i < t.length ==> t[i] == \old(t[i-1]))));
	  @ decreases j;
	  @*/
      for (int j=t.length-1 ; j > 0 ; j--) {
	  t[j] = t[j-1];
	}
    }
}


/*
Local Variables: 
compile-command: "make Arrays"
End: 
*/

