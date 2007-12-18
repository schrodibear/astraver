
//@+ ArithOverflow = no

/*@ axiom mean_1 : 
      \forall int x, y; x <= y ==> x <= x+(y-x)/2 <= y; */

class BinarySearch {

    /* binary_search(t,n,v) search for element v in array t 
       between index 0 and n-1
       array t is assumed to be sorted in increasing order
       returns an index i between 0 and n-1 where t[i] equals v, 
       or -1 if no element in t is equal to v  
    */
    
    /*@ requires 
      @   0 <= n <= t.length &&
      @   \forall int k1, k2; 0 <= k1 <= k2 <= n-1 ==> t[k1] <= t[k2];
      @ behavior correctness:
      @ ensures
      @   (\result >= 0 && t[\result] == v) ||
      @   (\result == -1 && \forall int k; 0 <= k < n ==> t[k] != v);
      @*/
    int binary_search(int t[], int n, int v) {
	int l = 0, u = n-1;
	/*@ loop_invariant 
	  @   0 <= l && u <= n-1 && 
	  @   \forall int k; 0 <= k < n ==> t[k] == v ==> l <= k <= u;
	  @ decreases 
	  @   u-l ;
	  @*/
	while (l <= u ) {
	    int m = l + (u - l) / 2;
	    if (t[m] < v) l = m + 1;
	    else if (t[m] > v) u = m - 1;
	    else return m; 
	}
	return -1;
    }

    /* idiomatic code, using t.length instead of n as argument */

    /*@ requires 
      @   t != null &&
      @   \forall int k1, k2; 0 <= k1 <= k2 <= t.length-1 ==> t[k1] <= t[k2];
      @ behavior correctness:
      @ ensures
      @   (\result >= 0 && t[\result] == v) ||
      @   (\result == -1 && \forall int k; 0 <= k < t.length ==> t[k] != v);
      @*/
    int binary_search2(int t[], int v) {
	int l = 0, u = t.length - 1;
	/*@ loop_invariant 
	  @   0 <= l && u <= t.length - 1 && 
	  @   \forall int k; 0 <= k < t.length ==> t[k] == v ==> l <= k <= u;
	  @ decreases 
	  @   u-l ;
	  @*/
	while (l <= u ) {
	    int m = l + (u - l) / 2;
	    if (t[m] < v) l = m + 1;
	    else if (t[m] > v) u = m - 1;
	    else return m; 
	}
	return -1;
    }

}
    
/*
Local Variables: 
compile-command: "make BinarySearch.io"
End: 
*/
