
int i;
int c;

/*@ requires i >=0 && c > 0
  @ ensures i==0
  @*/
void f() {
  /*@ invariant i >= 0
    @ variant i
    @*/
  while (i > 0) {
    if (i >= c) {
      i -= c;
    }
    else
      i--;
  }
}
