
int f () {
  int x = 1;
  L:
  x = 2;
  //@ assert \at(x,L) == x - 1;
  return x;
 }
