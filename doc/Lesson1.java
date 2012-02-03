// @+ CheckArithOverflow = no

/* lemma distr_right:
  @   \forall integer x y z; x*(y+z) == (x*y)+(x*z);
  @*/

/* lemma distr_left:
  @   \forall integer x y z; (x+y)*z == (x*z)+(y*z);
  @*/


public class Lesson1 {

    /*@ ensures \result >= x && \result >= y &&
      @    \forall integer z; z >= x && z >= y ==> z >= \result;
      @*/
    public static int max(int x, int y) {
        if (x>y) return x; else return y;
    }

    /*@ requires x >= 0;
      @ ensures
      @   \result >= 0 && \result * \result <= x
      @   && x < (\result + 1) * (\result + 1);
      @*/
    public static int sqrt(int x) {
	int count = 0, sum = 1;
	/*@ loop_invariant
	  @   count >= 0 && x >= count*count &&
	  @   sum == (count+1)*(count+1);
	  @*/
	while (sum <= x) {
	    count++;
	    sum = sum + 2*count+1;
	}
	return count;
    }

}
