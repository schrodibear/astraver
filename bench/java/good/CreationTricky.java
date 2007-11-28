
/* from JLS p 244
 */ 

class Super {

    Super() { printThree(); }

    void printThree() { Out.print(-1); }

}

class Test extends Super {

    int three = 3;

    // Krakatoa bug: should be implicit
    Test () { super(); }

    public static void test () {
	Test t = new Test();
	t.printThree();
	//@ assert Out.count == 2 && Out.data[0] == 0 && Out.data[1] == 3;
    }

    void printThree() { Out.print(three); }

}

// ghost model of output channel
class Out {

    public static int data[] = new int [10];
    static int count = 0;

    /*@ assigns data[count];
      @ ensures count == \old(count) + 1
      @     && data[\old(count)] == v;
      @*/
    static void print(int v) {
	data[count] = v;
	v++;
    }

}

