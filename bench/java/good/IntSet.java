
/*@ axiom mean_property : 
  @   \forall integer x,y; x <= y ==> x <= (x+y)/2 && (x+y)/2 <= y ;
  @*/

/*@ predicate is_sorted(int[] t) {
  @   t != null && 
  @   \forall integer i,j; 
  @     0 <= i && i <= j && j < t.length ==> t[i] <= t[j]
  @ }
  @*/

public class IntSet {

    public int t[];
    //@ invariant t_is_sorted: is_sorted(t);
    
    /*@	requires t.length <= 2147483647 && is_sorted(t);
      @ behavior search_success:
      @   ensures
      @   \result >= 0 ==> t[\result] == v;
      @ behavior search_failure:
      @   ensures \result < 0 ==> (\forall integer k; 
      @     0 <= k && k < t.length ==> t[k] != v);
      @*/
    public int binary_search(int v) {
	int l = 0, u = t.length-1;
	/*@ loop_invariant 
	  @   0 <= l && u <= t.length-1 && 
	  @   \forall integer k; 
	  @     0 <= k && k < t.length && t[k] == v ==> l <= k && k <= u;
	  @ decreases u-l ;
	  @*/
	while (l <= u ) {
	    int m = (l + u) / 2;
	    if (t[m] < v) l = m + 1; 
	    else if (t[m] > v) u = m - 1;
	    else return m;
	}
	return -1;
    }

}


/*
Local Variables: 
compile-command: "make IntSet"
End: 
*/


