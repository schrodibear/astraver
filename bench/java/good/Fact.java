//@+ CheckArithOverflow = no

public class Fact {

    /*@ requires n >= 0;
      @ decreases n;
      @*/
    public static long f(int n) {
	if (n <= 1) return 1;
        return n * f(n-1);
    }
}

