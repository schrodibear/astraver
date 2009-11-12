
// the following pragma allows to ignore potential arithmetic overflow
#pragma JessieIntegerModel(exact)



/*@ requires n >= 0;
  @ decreases n; 
  @*/
int even(int n);

/*@ requires n >= 0;
  @ decreases n; 
  @*/
int odd(int n);

int even(int n) {
  if (n == 0) return 1;
  return ! odd(n-1);
}

int odd(int n) {
  if (n == 0) return 0;
  return ! even(n-1);
}


/*@ predicate R(real x, real y) = 0.0 <= y && y-x >= 1.0;
  @*/

/*@ decreases y for R;
  @*/
int f(double y) {
  int n = 0;
  double x = y;
  if (x <= 1.0) return n;
  n = f(x - 2.0);
  /*@ loop variant x for R;
    @*/
  while (x >= 10.0) {
    n++ ; x -= 1.0; 
  }
  return n;
}
  
  
  
/* 
Local Variables:
compile-command: "LC_ALL=C make decreases"
End:
*/
