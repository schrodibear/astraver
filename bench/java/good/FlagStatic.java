
/* Dijkstra's dutch flag */

//@ predicate is_color(int c) { FlagStatic.BLUE <= c && c <= FlagStatic.RED }

/*@ predicate is_color_array(int t[]) { 
  @   t != null && 
  @   \forall int i; 0 <= i && i < t.length ==> is_color(t[i])
  @ }
  @*/

/*@ predicate is_monochrome(int t[],integer i, integer j, int c) {
  @   \forall int k; i <= k && k < j ==> t[k] == c
  @ }
  @*/



class FlagStatic {
    
    public static final int BLUE = 1, WHITE = 2, RED = 3;
    

    /*@ requires t != null && 0 <= i && i <= j && j <= t.length ;
      @ behavior decides_monochromatic:
      @   ensures \result <==> is_monochrome(t,i,j,c);
      @*/
    public static boolean isMonochrome(int t[], int i, int j, int c) {
    	/*@ loop_invariant i <= k && 
	  @   (\forall int l; i <= l && l < k ==> t[l]==c);
    	  @ decreases j - k;
	  @*/
	for (int k = i; k < j; k++) if (t[k] != c) return false;
	return true;
    }

    /*@ requires 0 <= i && i < t.length && 0 <= j && j < t.length;
      @ behavior i_j_swapped:
      @   assigns t[i],t[j];
      @   ensures t[i] == \old(t[j]) && t[j] == \old(t[i]);
      @*/
    private static void swap(int t[], int i, int j) {
	int z = t[i];
	t[i] = t[j];
	t[j] = z;
    }

    /*@ requires
      @   is_color_array(t); 
      @ behavior sorts:
      @   ensures 
      @     (\exists int b,r; is_monochrome(t,0,b,BLUE) &&
      @                       is_monochrome(t,b,r,WHITE) &&
      @                       is_monochrome(t,r,t.length,RED));
      @*/
    public static void flag(int t[]) {
	int b = 0;
	int i = 0;
	int r = t.length;
	/*@ loop_invariant
	  @   is_color_array(t) &&
	  @   0 <= b && b <= i && i <= r && r <= t.length &&
	  @   is_monochrome(t,0,b,BLUE) &&
	  @   is_monochrome(t,b,i,WHITE) &&
          @   is_monochrome(t,r,t.length,RED);
	  @ decreases r - i; 
	  @*/
	while (i < r) {
	    switch (t[i]) {
	    case BLUE:  
		swap(t,b++, i++);
		break;	    
	    case WHITE: 
		i++; 
		break;
	    case RED: 
		swap(t,--r, i);
		break;
	    }
	}
    }
}



/*
Local Variables: 
compile-command: "make FlagStatic.io"
End: 
*/