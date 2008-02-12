class Gcd {

    /*@ requires x >= 0 && y >= 0;
      @ behavior resultIsGcd: 
      @   ensures isGcd(x,y,\result) ;
      @ behavior bezoutProperty:
      @   ensures \exists integer a,b; a*x+b*y == \result;
      @*/
    int gcd(int x, int y);

        //@ ghost integer a = 1, b = 0, c = 0, d = 1;

        /*@ loop_invariant 
          @    x >= 0 && y >= 0 &&  
	  @    (\forall integer d ;  isGcd(x,y,d) ==> 
	  @        isGcd(\at(x,Pre),\at(y,Pre),d)) && 
          @    a*\at(x,Pre)+b*\at(y,Pre) == x && 
          @    c*\at(x,Pre)+d*\at(y,Pre) == y ;
          @ decreases y;
          @*/
        while (y > 0) {
            int r = x % y;
            //@ ghost integer q = x / y;
            x = y;
            y = r;
            //@ ghost integer ta = a, tb = b;
            //@ ghost a = c; 
	    //@ ghost b = d;
            //@ ghost c = ta - c * q;
            //@ ghost d = tb - d * q;
        }

        return x;
    }

}

