
public class Switch {

    /*@ behavior normal:
      @   assigns \nothing;
      @   ensures (n==0 || n==1) <==> \result == 0;
      @*/
    public static int test1 (int n) {
	int r;
	switch(n) {
	case 0:
	case 1:
	    r = 0;
	    break;
	default:
	    r = 2;
	}
	return r;
    }

    /*@ behavior normal:
      @   assigns \nothing;
      @   ensures ((n==4 || n==7) <==> \result == 1) && 
      @            ((n==0 || n==1) <==> \result == 0);
      @*/
    public static int test2 (int n) {
	int r;
	switch(n) {
	case 0:
	case 1:
	    r = 0;
	    break;
	case 4:
	case 7:
	    r = 1;
	    break;
	case 12:
	default:
	case 26:
	    r = 2;
	}
	return r;
    }

}

/*
Local Variables: 
compile-command: "make Switch.io"
End: 
*/

