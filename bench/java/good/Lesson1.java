
/* complements for non-linear integer arithmetic */

//@ axiom zero_right: \forall integer x; x*0 == 0;
//@ axiom zero_left: \forall integer x; 0*x == 0;
//@ axiom one_right: \forall integer x; x*1 == x;
//@ axiom one_left: \forall integer x; 1*x == x;
//@ axiom two_right: \forall integer x; x*2 == x+x;
//@ axiom two_left: \forall integer x; 2*x == x+x;

/*@ axiom distr_right: 
  @   \forall integer x,y,z; x*(y+z) == (x*y)+(x*z);
  @*/

/*@ axiom distr_left: 
  @   \forall integer x,y,z; (x+y)*z == (x*z)+(y*z);
  @*/

/*@ axiom sqr_short_elim: 
  @   \forall integer x; x*x <= 32760 ==> x <= 180;
  @*/

/*@ axiom sqr_short_intro: 
  @   \forall integer x; 0 <= x && x <= 181 ==> x*x <= 32761;
  @*/

/*@ axiom sqr_int_elim: 
  @   \forall integer x; x*x <= 2147395599 ==> x <= 46339;
  @*/

/*@ axiom sqr_int_intro: 
  @   \forall integer x; 0 <= x && x <= 46340 ==> x*x <= 2147395600;
  @*/


public class Lesson1 {

    /*@ behavior result_ge_x:
      @   ensures \result >= x; 
      @ behavior result_ge_y:
      @   ensures \result >= y; 
      @ behavior result_is_lub:
      @   ensures \forall integer z; z >= x && z >= y ==> z >= \result;
      @*/
    public static int max(int x, int y) {
	if (x>y) return x; else  return y; 
    }
    
    /*@ requires x >= 0 && x <= 32760;
      @ ensures \result >= 0 && \result * \result <= x 
      @    && x < (\result + 1) * (\result + 1);
      @*/
    public static short short_sqrt(short x) {
	short count = 0, sum = 1;
    	/*@ loop_invariant 
	  @   count >= 0 && x >= count*count &&
          @   sum == (count+1)*(count+1) &&
	  @   count <= 180 && sum <= 32761;
	  @ decreases x - sum;
	  @*/
	while (sum <= x) { 
	    count++;
	    //@ assert (count*count)+2*count+1 == (count+1)*(count+1);
	    sum += 2*count+1;
	}
	return count;
    }   
  
    /*@ requires x >= 0 && x <= 2147395599;
      @ behavior result_is_sqrt: 
      @   ensures \result >= 0 && \result * \result <= x 
      @      && x < (\result + 1) * (\result + 1) ;
      @*/
    public static int sqrt(int x) {
	int count = 0, sum = 1;
    	/*@ loop_invariant 
	  @   count >= 0 && x >= count*count &&
          @   sum == (count+1)*(count+1) &&
	  @   count <= 46339 && sum <= 2147395600;
	  @ decreases x - sum;
	  @*/
	while (sum <= x) {
	    count++;
	    //@ assert (count*count)+2*count+1 == (count+1)*(count+1);
	    sum += 2*count+1;
	}
	return count;
    }   
  
}

/*
Local Variables: 
compile-command: "make Lesson1"
End: 
*/
