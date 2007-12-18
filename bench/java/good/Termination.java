//@+ ArithOverflow = yes

class Termination {

    void loop1(int n) { 
	//@ decreases n;
	while (n > 0) n--; 
    }

    void loop2(int n) { 
	//@ decreases 100-n;
	while (n < 100) n++; 
    }

    //@ ensures \result == 0;
    int loop3() {
	int i = 100;
	/*@ loop_invariant 0 <= i <= 100;
	  @ decreases i;
	  @*/
	while (i > 0) i--;
	return i;
    }

}

