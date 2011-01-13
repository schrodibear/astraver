/* File Muller.java */

//@+ CheckArithOverflow = no
//@+ SeparationPolicy = Regions

//@ import tests.spec.NumOfPos;

/*@ lemma num_of_pos_strictly_increasing{L} :
  @   \forall integer i j k l, int t[];
  @       j < k && k <= l && t[k] > 0 ==> 
  @       num_of_pos(i,j,t) < num_of_pos(i,l,t);
  @*/

public class Muller {

    /*@ requires t!=null;
      @*/
    public static int[] m(int t[]) {
	int count = 0;
	
	/*@ loop_invariant
	  @    0 <= i <= t.length && 
	  @    0 <= count <= i && 
	  @    count == num_of_pos(0,i-1,t) ; 
	  @ loop_variant t.length - i;
	  @*/
	for (int i=0 ; i < t.length; i++) if (t[i] > 0) count++;
	
	int u[] = new int[count];
	count = 0;
	
	/*@ loop_invariant
	  @    0 <= i <= t.length && 
	  @    0 <= count <= i && 
	  @    count == num_of_pos(0,i-1,t);
	  @ loop_variant t.length - i;
	  @*/
	for (int i=0 ; i < t.length; i++) {
	    if (t[i] > 0) u[count++] = t[i];
	}
	return u;
    }
}

/* End of file Muller.java */
