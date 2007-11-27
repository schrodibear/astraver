
/*@ axiom mean_property : 
  @   \forall integer x, y; x <= y ==> x <= (x+y)/2 && (x+y)/2 <= y; */


/*@ predicate sorted(long t[]) {
  @   \forall integer i,j; 0 <= i && i <= j && j < t.length ==>
  @          t[i] <= t[j] } */

public class Search {

    long t[];
    // pb with recursive def of type and logic in Jessie
    // @ invariant t_sorted: t != null && sorted(t);

    /*@ requires t != null && t.length < 2147483647 && sorted(t);
      @ behavior search_success:
      @   ensures \result >= 0 ==> t[\result] == v;
      @ behavior search_failure:
      @   ensures \result < 0 ==> 
      @     \forall integer k; 0 <= k && k < t.length ==> t[k] != v;
      @*/
    int binary_search(long v) {
	int l = 0, u = t.length-1;
	/*@ loop_invariant 
	  @   0 <= l && u <= t.length-1 &&
	  @     \forall integer i; 
	  @        0 <= i && i < t.length ==> t[i] == v ==> l <= i && i <= u;
	  @ decreases u-l ;
	  @*/
	while (l <= u ) {
	    int m = (l + u) / 2;
	    //@ assert l <= m && m <= u;
	    if (t[m] < v) l = m + 1;
	    else if (t[m] > v) u = m - 1;
	    else return m;
	}
	return -1;
    }
}


/*
Local Variables: 
compile-command: "make Search"
End: 
*/

