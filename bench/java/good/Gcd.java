/* complements for non-linear integer arithmetic */

//@ axiom zero_right: \forall integer x; x*0 == 0;  
//@ axiom zero_left: \forall integer x; 0*x == 0; 
//@ axiom one_right: \forall integer x; x*1 == x; 
//@ axiom one_left: \forall integer x; 1*x == x; 
//@ axiom two_right: \forall integer x; x*2 == x+x; 
//@ axiom two_left: \forall integer x; 2*x == x+x; 

/*@ axiom distr_right: 
  @   \forall integer x,y,z; x*(y+z) == (x*y)+(x*z); 
  @*/

/*@ axiom distr_left: 
  @   \forall integer x,y,z; (x+y)*z == (x*z)+(y*z);
  @*/

/*@ predicate divides(integer x, integer y) {
  @   \exists integer q; y == q*x
  @ }
  @*/

/*@ axiom div_mod_property:
  @  \forall integer x,y; 
  @    x >=0 && y > 0 ==> x%y  == x - y*(x/y);  
  @*/

/*@ axiom mod_property:
  @  \forall integer x,y; 
  @    x >=0 && y > 0 ==> 0 <= x%y && x%y < y; 
  @*/

class Gcd {

    /*@ requires x >= 0 && y >= 0;
      @ behavior divides_both:
      @   ensures divides(\result,x) && divides(\result,y);
      @ behavior is_greatest_divisor:
      @   ensures \forall integer z;
      @     z>0 && divides(z,x) && divides(z,y) ==> z>=\result;
      @ behavior bezout_property:
      @   ensures \exists integer a,b; a*x+b*y == \result;
      @*/
    int gcd(int x, int y) {
        //@ ghost int a = 1, b = 0, c = 0, d = 1;
        /*@ loop_invariant 
          @    x >= 0 && y >= 0 &&  
          @    a*\old(x)+b*\old(y) == x && 
          @    c*\old(x)+d*\old(y) == y ;
          @ decreases y;
          @*/
        while (y > 0) {
            int r = x % y;
            //@ ghost int q = x / y;
            x = y;
            y = r;
            //@ ghost int ta = a, tb = b;
            //@ ghost a = c; 
	    //@ ghost b = d;
            //@ ghost c = ta - c * q;
            //@ ghost d = tb - d * q;
        }
        return x;
    }

}


/*
Local Variables: 
compile-command: "make Gcd.io"
End: 
*/

