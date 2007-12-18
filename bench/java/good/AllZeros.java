
class AllZeros {

    /*@ requires t != null;
      @ ensures \result <==> \forall integer i; 0<=i<t.length ==> t[i]==0; 
      @*/
    static boolean all_zeros(int t[]) {
	/*@ loop_invariant 
	  @  0 <= k <= t.length && 
	  @  \forall integer i; 0 <= i < k ==> t[i]==0;
	  @ decreases t.length - k;
	  @*/
	for (int k = 0; k < t.length; k++) if (t[k]!=0) return false;
	return true;
    }
}
