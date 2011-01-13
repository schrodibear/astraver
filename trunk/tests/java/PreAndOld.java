

//@+ CheckArithOverflow = no

//@ logic integer f{L}(integer n) = n+PreAndOld.y;


class PreAndOld {

    static int y;
    
    /*@ ensures \result == \old(f(x))
      @      && \result == f{Old}(x)
      @      && \result == \at(f(x),Pre);
      @*/
    int g(int x) {
        int tmp = y;
        y = 12;
        return x+tmp;
    }
}
  

