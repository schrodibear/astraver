
class A {

    int n;
}

class B {

    int m(A x) {
	return x.n;
    }

    void m1(int[] t) {
	for (int i = 0; i < t.length; i++)
	    t[i] = 0;
    }

    int main() {
	A x = new A();
	int[] t = new int[3];
	m1(t);
	return m(x);
    }

}
