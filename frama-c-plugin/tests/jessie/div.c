

//@ logic integer parent(integer i) = (i-1)/2;

//@ logic integer left(integer i) = 2*i+1;

//@ logic integer right(integer i) = 2*i+2;

//@ lemma Parent_left: \forall integer i; i >= 0 ==> parent(left(i)) == i;

//@ lemma Parent_right: \forall integer i; i >= 0 ==> parent(right(i)) == i;



// Note: useless with Why3
/*@ lemma mult_div: \forall integer i, j; i > 0 && j >=0 ==> (i * j) / i == j;
  @ */

/*@ requires x > 0;
  @ ensures 4 * x / 4 >= 0;
  @*/
int f(int x) {
  return 10/x;
}
