
class VA {

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
