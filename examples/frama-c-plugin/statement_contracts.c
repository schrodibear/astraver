


/*@ behavior b: ensures \true;
  @*/
void f() {
  int x;
  //@ assigns x; ensures x == 0;
  x = 0;
  //@ assigns x; ensures x == 1;
  x = 1;
  //@ for b: assert \false;
}

/* Frama-C BTS 0072 */

void myfun(int p){
    p = 1;
    /*@ requires p==1;
      @ ensures \old(p)==p-1;
      @*/
    p = 2;
}
