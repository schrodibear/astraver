

//@+ ArithOverflow = no
//@+ InvariantPolicy = Arguments
//@+ NonNullByDefault = yes

class C { int x; }

class NonNullByDefault {
    
    int[] t;
    C c;

    int[] m1() {
	return t;
    }
    
    int[] /*@ nullable @*/ m1bis() {
	return null;
    }
    
    C m2() {
	return c;
    }
    
    C /*@ nullable @*/ m2bis() {
	return null;
    }
    
    C m2ter() {
	return new C();
    }

    void m3(int[] pt, C pc) {
	int n = pt.length;
	this.t = pt;
	int m = pc.x;
	this.c = c;
    }
    
}
