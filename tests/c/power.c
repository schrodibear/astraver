

// int model: unbounded mathematical integers
#pragma JessieIntegerModel(math)


/*@ axiomatic Power {
  @   logic integer power(integer x, integer n);
  @ }
  @*/
#pragma JessieBuiltin(power, "\\int_pow")

/*@ lemma power_even:
  @   \forall integer x,n; n >= 0 && n % 2 == 0 ==>
  @     power(x,n) == power(x*x,n/2);
  @*/

/*@ lemma power_odd:
  @   \forall integer x,n; n >= 0 && n % 2 != 0 ==>
  @     power(x,n) == x*power(x*x,n/2);
  @*/


// recursive implementation

/*@ requires 0 <= n;
  @ decreases n;
  @ ensures \result == power(x,n);
  @*/
long rec(long x, int n) {
  if (n == 0) return 1;
  long r = rec(x, n/2);
  if ( n % 2 == 0 ) return r*r;
  return r*r*x;
}


// non-recursive implementation

/*@ requires 0 <= n;
  @ ensures \result == power(x,n);
  @*/
long imp(long x, int n) {
  long r = 1, p = x;
  int e = n;

  /*@ loop invariant
    @   0 <= e && r * power(p,e) == power(x,n);
    @ loop variant e;
    @*/
  while (e > 0) {
    if (e % 2 != 0) r *= p;
    p *= p;
    e /= 2;
  }
  return r;
}

