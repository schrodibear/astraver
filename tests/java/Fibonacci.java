//@+ CheckArithOverflow = no

/*@ predicate isfib(integer x, integer r) {
  @  axiom isfib0: isfib(0,0);
  @  axiom isfib1: isfib(1,1);
  @  axiom isfibn: 
  @   \forall integer n r p; 
  @     n >= 2 && isfib(n-2,r) && isfib(n-1,p) ==> isfib(n,p+r);
  @ }
  @*/ 



public class Fibonacci {

    /*@ requires n >= 0;
      @ ensures isfib(n, \result); 
      @*/
    public long Fib(int n) {
	long y=0, x=1, aux;

	/*@ loop_invariant 0<= i <= n && isfib(i+1,x) && isfib(i,y);
	  @ loop_variant n-i;
	  @*/
	for(int i=0; i < n; i++) {
	    aux = y;
	    y = x;
	    x = x + aux;
	}
	return y;
    }
}

