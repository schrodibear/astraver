/*@ type foo = int; */

/*@
  requires y <= 10;
  ensures \forall foo x; x == y ==> x <= \result; */
int f(int y) { return y+2; }
