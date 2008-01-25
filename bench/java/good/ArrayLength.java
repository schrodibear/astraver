
class ArrayLength {

    /*@ requires t != null;
      @*/
    int getLength(int[] t) {
	int[] p = new int[0];
	// System.out.println(p.length);
	return t.length;
    }

    public static void main(String[] args) {
	ArrayLength al = new ArrayLength();
	al.getLength(new int[12]);
    }

}


/*
Local Variables: 
compile-command: "make ArrayLength"
End: 
*/

