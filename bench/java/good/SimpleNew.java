
public class SimpleNew {

    int simple_val;

    /*@ behavior normal:
      @   assigns \nothing; // not `this.simple_val'; 
      @   ensures this.simple_val == 0;
      @*/
    SimpleNew() {
	/* this(0); */
	simple_val = 0;
    }

    /*@ behavior normal:
      @   assigns \nothing;
      @   ensures this.simple_val == n;
      @*/
    SimpleNew(int n) {
	simple_val = n;
    }

    /*@ behavior normal:
      @   assigns \nothing;
      @   ensures this.simple_val == n + m;
      @*/
    SimpleNew(int n,int m) {
	/* this(n+m); */
	simple_val = n+m;
    }

    /*@ behavior normal:
      @   ensures \result == 17;
      @*/
    public static int test1() {
	SimpleNew t = new SimpleNew(17);
	return t.simple_val;
    }

    /*@ behavior normal:
      @   ensures \result == 0;
      @*/
    public static int test2() {
	SimpleNew t = new SimpleNew();
	return t.simple_val;
    }

    /*@ behavior normal:
      @   assigns \nothing;
      @   ensures \result == 17;
      @*/
    public static int test3() {
	SimpleNew t = new SimpleNew(10,7);
	return t.simple_val;
    }
}


/*
Local Variables: 
compile-command: "make SimpleNew.io"
End: 
*/
