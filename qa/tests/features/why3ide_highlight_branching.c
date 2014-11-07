int main(void)
{
  int a, b, c, d, e;
  
  if (a) {
    if (!b && (c || d)) {
      //@ assert c || d;
      if ((c | d) == 0 || (d | c) == 0) {
        //@ assert !b;
      }
    } else {
      if (a && c == d && ! a > c || a && e) {
        a = 0;
        c = a;
        d = a;
        /*@ loop invariant a < 100 && c == d && d == 0;
          @ loop variant 100 - a + c + d;
          @*/
        while (a + c + d < 10) {
          //@ assert a < 10;
          a++;
        }
        //@ assert a < 100;
      }
      a = 0;
      b = 0;
      /*@ loop invariant a + b < 120;
        @ loop variant 121 - a - b;
        @*/
      while (a < 10 && b < 100) {
         //@ assert a < 10 && b < 100;
         a++;
         b++;
         //@ assert a < 11 && b < 101;
      }
      //@ assert a + b < 120;
    }
  } else {
    a = 0;
    /*@ loop invariant a < 100;
      @ loop variant 100 - a;
     */
    do {
      a++;
      //@ assert a < 101;
    } while (a < 10);
    //@ assert a < 101;
  }
  
  //@ assert a || !a;
  return 0;
}
