
public class Lesson1 {

    /*@ ensures \result >= x && \result >= y &&
      @    \forall integer z; z >= x && z >= y ==> z >= \result;
      @*/
    public static int max(int x, int y) {
        if (x>y) return x; else return x; 
    }
}
