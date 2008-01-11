
//@ logic integer num_of_pos(integer i,integer j,int t[]) reads t[i..j] ;

/* @ axiom num_of_pos_empty :
  @   \forall integer i, j; \forall int t[];
  @       i > j ==> num_of_pos(i,j,t) == 0;
  @*/
 
/* @ axiom num_of_pos_true_case :
  @   \forall integer i, j, k; \forall int t[];
  @       i <= j && t[j] > 0 ==> 
  @         num_of_pos(i,j,t) == num_of_pos(i,j-1,t) + 1;
  @*/

/* @ axiom num_of_pos_false_case :
  @   \forall integer i, j, k; \forall int t[];
  @       i <= j && ! (t[j] > 0) ==> 
  @         num_of_pos(i,j,t) == num_of_pos(i,j-1,t);
  @*/

/* @ axiom num_of_pos_strictly_increasing:
  @   \forall integer i, j, k, l; \forall int t[];
  @       j < k && k <= l && t[k] > 0 ==> num_of_pos(i,j,t) < num_of_pos(i,l,t);
  @*/

public class Muller {

    /*@ requires t!=null;
      @*/
    public static int[] m(int t[]) {
	int count = 0;
	
	/*@ loop_invariant
	  @    0 <= i && i <= t.length && 
	  @    0 <= count && count <= i && 
	  @    count == num_of_pos(0,i-1,t) ; 
	  @ decreases t.length - i;
	  @*/
	for (int i=0 ; i < t.length; i++) if (t[i] > 0) count++;
	
	int u[] = new int[count];
	count = 0;
	
	/*@ loop_invariant
	  @    0 <= i && i <= t.length && 
	  @    0 <= count && count <= i && 
	  @    count == num_of_pos(0,i-1,t);
	  @ decreases t.length - i;
	  @*/
	for (int i=0 ; i < t.length; i++) {
	    if (t[i] > 0) u[count++] = t[i];
	}
	return u;
    }
    
}

/*
Local Variables: 
compile-command: "make Muller.io"
End: 
*/
