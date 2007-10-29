

class Literals {

    public static final int x = 0xbad;

    /*@ behavior ok: ensures \result == 0xd;
      @*/
    int f() {
	int x = 0xbad;
	return 015;
    }
}

/*
Local Variables: 
compile-command: "make Literals"
End: 
*/


