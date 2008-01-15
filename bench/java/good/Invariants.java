//////////////////////////////////////////////////////////////////////

class C1 {

    int[] t;
    //@ invariant C1_t_inv: t != null && t.length >= 1;

    void m(int[] p) {
	p[0] = 1;
   }

    void main() {
	m(t);
    }

}

//////////////////////////////////////////////////////////////////////

class C2 {

    static int[] t;
    //@ static invariant C2_t_inv: t != null && t.length >= 1;

    void m(int[] p) {
	p[0] = 1;
   }

    void main() {
	m(t);
    }

}

//////////////////////////////////////////////////////////////////////

class C3 {

    static Object t;
    //@ static invariant C3_t_inv: t != null;

    void m() {
	t = new Object();
	// INDEPENDENT PROBLEM: assertion not prouved (add '<> null' in ths post of <new> in jessie.why ?)
	//@ assert t != null; 
   }

}

//////////////////////////////////////////////////////////////////////

class C4 {
    static int[] t; 
    //@ static invariant C4_t_inv: t != null && t.length == 10;
}

class C5 {
    void m() {
	int i = C4.t[0]; 
    }
}



/*
Local Variables: 
compile-command: "make Invariants"
End: 
*/


