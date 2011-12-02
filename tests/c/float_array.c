#define EPS1 0x1p-53
#define UPPER 0x1p0
#define n 10

//@ predicate bounded(real z, real bound) = \abs(z) <= bound;

double x;

/*@
  @ requires bounded(d, UPPER);
  @ requires \round_error(d) == 0;
  @
  @ ensures \abs(x - (d + 1.0)) <= EPS1;
  @ ensures \round_error(x) <= EPS1;
*/
void AffectDoubleDansX(double d) {
        x=d+1.0;
}

/*@
  @ requires \valid_range(X,0,n);
  @ requires bounded(d, UPPER);
  @ requires \round_error(d) == 0;
  @
  @ ensures \abs(X[1] - (d + 1.0)) <= EPS1;
  @ ensures \round_error(X[1]) <= EPS1;
  @ ensures \abs(X[2] - (d + 1.0)) <= EPS1;
  @ ensures \round_error(X[2]) <= EPS1;
*/
void AffectDoubleDansTab(double d, double X[]) {
        X[1]=d+1.0;
        X[2]=d+1.0;
        // assert X[1] == \round_double(\NearestEven,d+1.0);
}

/*@
  @ requires \valid_range(X,0,n);
  @ requires bounded(d, UPPER);
  @ requires \round_error(d) == 0;
  @
  @ ensures \abs(X[1] - (d + 1.0)) <= EPS1;
  @ ensures \round_error(X[1]) <= EPS1;
*/
void AffectDoubleDansTab1(double d, double X[]) {
        X[1]=d+1.0;
}

/*@
  @ requires \valid_range(X,0,n);
  @ requires bounded(d, UPPER);
  @ requires \round_error(d) == 0;
  @
  @ ensures \abs(X[0] - (d + 1.0)) <= EPS1;
  @ ensures \round_error(X[0]) <= EPS1;
*/
void AffectDoubleDansTab0(double d, double X[]) {
        X[0]=d+1.0;
        //@ assert X[0] == \round_double(\NearestEven,d+1.0);
        //@ assert \exact(X[0]) == d+1.0;
}
