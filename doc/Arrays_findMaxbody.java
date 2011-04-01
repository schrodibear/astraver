  public static int findMax(int[] t) {
      int m = t[0];
      int r = 0;
      /*@ loop_invariant 
	@   1 <= i && i <= t.length && 0 <= r && r < t.length &&
	@   m == t[r] && \forall integer j; 0<=j && j<i ==> t[j]<=t[r];
	@ loop_variant t.length-i;
	@*/
      for (int i=1; i < t.length; i++) {
	  if (t[i] > m) {
	      r = i; 
	      m = t[i];
	  }
      }
      return r;
  }

