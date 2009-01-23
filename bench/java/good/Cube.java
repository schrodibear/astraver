public class Cube {
  //@ requires x > 0;
  //@ ensures \result == x * x * x;
  public static int cube(int x) {
    int a = 1;
    int b = 0;
    int c = x;
    int z = 0;
    //@ maintaining a == 3*(x-c) + 1;
    //@ maintaining b == 3*(x-c)*(x-c);
    //@ maintaining z == (x-c)*(x-c)*(x-c);
    //@ decreasing c;
    while (c > 0) {
      z += a + b;
      b += 2*a + 1;
      a += 3;
      c--;
    }
    return z;
  }
}
