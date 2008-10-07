//@+ CheckArithOverflow = no

/*@ predicate isfib(integer x, integer r) {
  @  axiom isfib0: isfib(0,0);
  @  axiom isfib1: isfib(1,1);
  @  axiom isfibn: 
  @   \forall integer n r p; 
  @     isfib(n-2,r) ==> isfib(n-1,p) ==> isfib(n,p+r);
  @ }
  @*/ 



public class Fibonacci {

    int n; 
    int x;

    /*@ requires n > 0;
      @ ensures isfib(n, x); 
      @*/
    private int Fib() {
	int y = 0;
	int i = 1;
	int aux;
	x = 1;

	/*@
	  @ loop_invariant i <= n && isfib(i,x) && isfib(i-1,y);
	  @*/
	while (i < n) {
	    aux = y;
	    y = x;
	    x = x + aux;
	    i = i + 1;
	}
	return x;
    }
}

