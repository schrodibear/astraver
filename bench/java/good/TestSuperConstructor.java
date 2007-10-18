
class C {

    int i;

    /* @ behavior normal:
      @   assigns i;
      @   ensures i == j;
      @*/
    C (int j) {
	i = j;
    }
}


class TestSuperConstructor extends C {

    /* @ behavior normal:
      @   assigns i;
      @   ensures i == 12;
      @*/
    TestSuperConstructor() {
	super (12);
    }

}
