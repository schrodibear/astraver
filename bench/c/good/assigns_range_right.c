
int t[10];
int k;

/*@ requires 0 <= k < 10
  @ assigns  t[k..], k
  @ ensures  k == \old(k)
  @*/
void f() {
  int i;
  /*@ invariant k == \old(k)
    @ loop_assigns k, t[k..]
    @*/
  for (i = 0; i < 10; i++) {
    t[k] = i;
    k++;
    if (k<10) f();
    k--;
  }
}
