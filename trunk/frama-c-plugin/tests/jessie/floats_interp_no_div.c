
#define UPPER 0x1p500
#define LOWER 0x1p-53
#define EPS 0x1p-53

//@ predicate bounded(real z, real bound) = -bound <= z <= bound;

/*@ requires x1 <= z <= x2;
  @ requires bounded(x1,UPPER);
  @ requires bounded(x2,UPPER);
  @ requires bounded(v,UPPER);
  @ // requires bounded(y1,UPPER);
  @ // requires bounded(y2,UPPER);
  @ // requires x2 - x1 >= LOWER;
  @ // requires y2 - y1 >= LOWER;
  @ requires 
  @   \let slope = (y2 - y1) / (x2 - x1);
  @     bounded(slope,UPPER) && \abs(v - slope) <= EPS*\abs(slope);
  @ ensures
  @     \let slope = (y2 - y1) / (x2 - x1) ;
  @     \let exact_result = y1 + slope * (z - x1) ;
  @     \abs(\result - exact_result) <= 0x1p-1 ;
  @*/
double interp_lin(double x1, double x2, double y1, double y2, 
                  double v, double z) {
  double a = z-x1;
  //@ assert \abs(a - (z-x1)) <= EPS*\abs(z-x1);
  //@ assert bounded(a,0x1p502);
  double b = v*a;
  //@ assert \abs(b - v*a) <= 0x1p-10*\abs(v*a);
  /*@ assert   
    @   \let slope = (y2 - y1) / (x2 - x1);
    @   \abs(b - slope*(z-x1)) <= 0x1p-25*\abs(slope*(z-x1));
    @*/
  return y1+b;
}

/*
Local Variables:
compile-command: "PPCHOME=../.. LC_ALL=C make floats_interp_no_div"
End:
*/
