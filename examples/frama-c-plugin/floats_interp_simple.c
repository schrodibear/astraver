
#define UPPER 0x1p100
#define LOWER 0x1p-53
#define EPS 0x1p-53

//@ predicate bounded(double z, real bound) = -bound <= z <= bound;


// Coq needed
/*@ lemma div_bounds :
  @   \forall real a,b;
  @   0.0 < b && 0.0 <= a <= b ==> 0.0 <= a/b <= 1.0;
  @*/

// known by Gappa
//@ lemma round_0 : \round_double(\NearestEven,0.0) == 0.0;
//@ lemma round_1 : \round_double(\NearestEven,1.0) == 1.0;

// proved by SMT provers from the 3 lemmas above, and monotonicity of rounding
// which is in floats_common.why
/*@ lemma round_div :
  @   \forall real a,b;
  @   0.0 < b && 0.0 <= a <= b ==> 0.0 <= \round_double(\NearestEven,a/b) <= 1.0;
  @*/

/*@ requires x1 < z <= x2;
  @ requires bounded(x1,UPPER);
  @ requires bounded(x2,UPPER);
  @ requires bounded(y1,UPPER);
  @ requires bounded(y2,UPPER);
  @ requires x2 - x1 >= LOWER;
  @ requires y2 - y1 >= LOWER;
  @ behavior normalized:
  @   assumes z - x1 >= EPS; 
  @   ensures
  @     \let k = (z - x1)/(x2-x1) ;
  @     \let exact_result = y1 + k*(y2 - y1) ;
  @     \abs(\result - exact_result) <= 0x1p-1 ;
  @ behavior denormalized:
  @   assumes z - x1 < EPS; 
  @   ensures
  @     \let k = (z - x1)/(x2-x1) ;
  @     \let exact_result = y1 + k*(y2 - y1) ;
  @     \abs(\result - exact_result) <= 0x1p-1 ;
  @*/
double interp_lin(double x1, double x2, double y1, double y2, double z) {
  double b = x2 - x1;
  //@ assert LOWER <= b;
  //@ assert 0.0 < b;
  //@ assert \abs((b -(x2 - x1))/(x2-x1)) <= EPS;
  double a = z - x1;  
  //@ assert 0 <= z - x1 <= x2 - x1;
  //@ assert 0.0 <= a <= b;
  //@ for normalized: assert \abs((a -(z - x1))/(z-x1)) <= EPS;
  //@ for denormalized: assert \abs(a - (z - x1)) <= EPS;
  double k = a/b;
  //@ assert 0.0 <= k <= 1.0;
  //@ assert \let k2 = (z-x1)/(x2-x1) ; 0.0 <= k2 <= 1.0 ;
  /*@ for denormalized: 
    @   assert \let k2 = (z-x1)/(x2-x1) ; \abs(k - k2) <= 0x1p-51;
    @*/
  double c = y2 - y1;
  //@ assert \abs((c - (y2 - y1))/(y2-y1)) <= EPS;
  double r = y1+k*(y2-y1);
  /*@ for denormalized: assert
    @     \let k2 = (z - x1)/(x2-x1) ;
    @     \let exact_result = y1 + k2*(y2 - y1) ;
    @     \abs(r - exact_result) <= 0x1p-1 ;
    @*/
  /* @ for normalized: assert
    @     \let k2 = (z - x1)/(x2-x1) ;
    @     \let exact_result = y1 + k2*(y2 - y1) ;
    @     \abs(r - exact_result) <= 0x1p-1 ;
    @*/
  return r;
}

/*
Local Variables:
compile-command: "PPCHOME=../.. LC_ALL=C make floats_interp_simple"
End:
*/
