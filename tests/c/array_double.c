


double a[2];
double b[2];
double c[2];


/*@ requires
  \valid(a+(0..1)) &&
  \valid(b+(0..1)) &&
  \valid(c+(0..1)) &&
      \abs(b[0]) <= 1.0 &&
      \abs(b[1]) <= 1.0 &&
      \abs(c[0]) <= 1.0 &&
      \abs(c[1]) <= 1.0 ;
*/
void test() {
  a[0] = b[0] + c[0];
  a[1] = b[1] + c[1];
  //@ assert \abs(a[0] - (b[0] + c[0])) <= 0x1p-53;

}


/*
Local Variables:
compile-command: "make array_double.why3ide"
End:
*/
