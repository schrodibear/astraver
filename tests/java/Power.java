

// int model: unbounded mathematical integers
//@+ CheckArithOverflow = no


/*@ axiomatic Power {
  @   logic integer power(integer x, integer n);
  @   axiom power_0: \forall integer x; power(x,0) == 1;
  @   axiom power_s: \forall integer x n; power(x,n+1) == x*power(x,n);
  @ }
  @*/

/*@ lemma power_mul: 
  @   \forall integer x y n; n >= 0 ==> power(x*y,n) == power(x,n)*power(y,n);
  @*/

/*@ lemma power_even: 
  @   \forall integer x n; n >= 0 && n % 2 == 0 ==> power(x,n) == power(x*x,n/2);
  @*/

/*@ lemma power_odd: 
  @   \forall integer x n; n >= 0 && n % 2 != 0 ==> power(x,n) == x*power(x*x,n/2);
  @*/


class Power {

    // recursive implementation

    /*@ requires 0 <= n;
      @ decreases n;
      @ ensures \result == power(x,n);
      @*/
    static long rec(long x, int n) {
        if ( n == 0) return 1;
        long r = rec(x, n/2);
        if ( n % 2 == 0 ) return r*r;
        return r*r*x;
    }


    // non-recursive implementation

    /*@ requires 0 <= n;
      @ ensures \result == power(x,n);
      @*/
    static long imp(long x, int n) {
        long r = 1, p = x;
        int e = n;

        /*@ loop_invariant 
          @   0 <= e && r * power(p,e) == power(x,n);
          @ loop_variant e;
          @*/
        while (e > 0) {
            if (e % 2 != 0) r *= p;
            p *= p;
            e /= 2;
        }
        return r;
    }

}

