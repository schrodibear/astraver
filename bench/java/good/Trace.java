
class Trace {

    /* Example 1 
     * We want the message: 
     *  "assertion `x < 9' cannot be established"
     * localized on `x < 9' 
     */
    
    /*@ requires x > 0;
      @*/
    int f1(int x) {
	//@ assert x >= 0 && x < 9; 
	return x+1;
    }

    /* Example 2 
     * We want the message: 
     *  "post-condition `\result > 10' of function f2 cannot be established"
     * localized on `return x+1'
     * Bonus: all lines involved in the execution path should be ~underlined 
     */
    /*@ requires x > 0 && x < 100;
      @ behavior ok:
      @   ensures \result != 0 && \result > 10;  
      @*/
    int f2(int x) {
	int y;
	if (x<50) 
	    return x+1;
	else 
	    y = x-1;
	return y;
    }


    /* Example 3 
     * We want the message: 
     *  "pre-condition `x > 0' for call to function f3 cannot be established"
     * localized on `(f2 x)' 
     */
    /*@ requires x >= 0 && x < 50;
      @*/
    int f3(int x) {
	return f2(x);
    }


    /* Example 4 
     * Explanation expected: 
     *   "validity of loop invariant `0 <= y' at loop entrance"
     * localized on `while ...' 
     */
    void f4(int x) { 
	int y = x;
	/*@ loop_invariant 0 <= y && y <= x;
	  @ decreases y;
	  @*/
	while (y > 0)
	    {
	    y = y - 1;
	}
    }

    
    /* Example 5 
     * Explanation expected:
     *   "preservation of loop invariant `y = x'"
     * localized on the '}' closing the loop body 
     */
    
    void f5(int x) {
	int y = x;
	/*@ loop_invariant y == x;
	  @ decreases y;
	  @*/
	while (y > 0) {
	    y = y - 1;
	}
    }

    /* Example 6
     * Explanation expected:
     *   "arithmetic overflow"
     * localized on first "x", on "(byte)(x+1)" and on "(byte)(x+2)"
     */
    byte f6(byte x) {
	x += x+1;
	x = (byte)(x+1); 
	return (byte)(x+2);
    }
    
}



/*
Local Variables: 
mode: java
compile-command: "make Trace.goals"
End: 
*/
