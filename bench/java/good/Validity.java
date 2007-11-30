
class VA {

    VA();

    int n;
}

class VB {

    int m(VA x) {
	return x.n;
    }

    void m1(int[] t) {
	for (int i = 0; i < t.length; i++)
	    t[i] = 0;
    }

    int main() {
	VA y = new VA();
	int[] t = new int[3];
	m1(t);
	return m(y);
    }

}

class T {

    int p[];

    //@ requires t != null && t.length >= 1;
    static int m(int t[]) {
	return t[0];
    }

    //@ ensures \result == 0;
    public int test() {
	p = new int [1];
	return m(p);
    }
	
}



/*
Local Variables: 
compile-command: "make Validity.io"
End: 
*/

