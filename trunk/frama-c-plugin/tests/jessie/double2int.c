

//@ ensures \result == 65536.0;
double test() {
  return (double)65536;
}


/*@
behavior small:
    assumes f <= -65536.0;
    ensures \result == -65536;

behavior big:
    assumes f >= 65535.0;
    ensures \result == 65535;

behavior negative_fits:
    assumes -65536.0 < f < 0.0;
    ensures f <= \result < f+1;

behavior positive_fits:
    assumes 0.0 <= f < 65535.0;
    ensures f-1 < \result <= f;
*/
int double2int(double f) {
    int i;
    if      (f <= -65536.0)  i=-65536;
    else if (f >= 65535.0)   i=65535;
    else                     i=f;
    return i;
}


/*
Local Variables: 
compile-command: "make double2int"
End: 
*/
