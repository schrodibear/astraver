
/*@ axiom distr_right: 
  @   \forall int x,y,z; x*(y+z) == (x*y)+(x*z)
  @*/

/*@ axiom distr_left: 
  @   \forall int x,y,z; (x+y)*z == (x*z)+(y*z)
  @*/

public class Lesson1 {

    /*@ behavior result_ge_x:
      @   ensures \result >= x 
      @ behavior result_ge_y:
      @   ensures \result >= y 
      @ behavior result_is_lub:
      @   ensures \forall int z; z >= x && z >= y => z >= \result
      @*/
    public static int max(int x, int y) {
	if (x>y) return x; else  return y; 
    }
    
    /*@ requires x >= 0
      @ behavior result_is_sqrt: 
      @   ensures \result >= 0 && \result * \result <= x 
      @      && x < (\result + 1) * (\result + 1)
      @*/
    public static int sqrt(int x) {
	int count = 0, sum = 1;
    	/*@ loop_invariant 
	  @   count >= 0 && x >= count*count &&
          @   sum == (count+1)*(count+1)
	  @ decreases x - sum
	  @*/
	while (sum <= x) { 
	    count++;
	    sum = sum + 2*count+1;
	}
	return count;
    }   
  
}

/*
Local Variables: 
compile-command: "make Lesson1"
End: 
*/
