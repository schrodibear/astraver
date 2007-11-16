
    /*@ public normal_behavior
      @   requires t != null && 0 <= l && l <= t.length;
      @   ensures 
      @      \result <==> 0 <= i && i < l &&
      @      (\forall integer j; 0 <= j && j < l; t[j] <= t[i]);
      @*/
    public static /*@ pure @*/ boolean isMax(int[] t,int i,int l);

    /*@ public normal_behavior
      @   requires t != null && t.length >= 1;
      @   ensures isMax(t,\result,t.length) ;
      @*/
    public static int findMax2(int[] t) {
        int m = t[0];
        int r = 0;
        /*@ loop_invariant 
          @   1 <= i && i <= t.length && m == t[r] && isMax(t,r,i) ;
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
