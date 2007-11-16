
/*@ requires t != null ;
  @ ensures 
  @   \forall integer i; 0 < i && i < t.length ==> t[i] == \old(t[i-1]);
  @*/
public static void shift(int[] t) {
  /*@ loop_invariant 
    @  j < t.length &&
    @  (t.length > 0 ==>
    @    0 <= j && 
    @    \forall integer i; 0 <= i && i <= j ==> t[i] == \old(t[i]) &&
    @    \forall integer i; 
    @         j < i && i < t.length ==> t[i] == \old(t[i-1])));
    @ decreases j;
    @*/
  for (int j=t.length-1 ; j > 0 ; j--) {
      t[j] = t[j-1];
  }
}
