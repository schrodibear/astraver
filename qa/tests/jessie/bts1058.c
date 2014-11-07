
int f(void) {

  int x = 0;
 L:
  x++;
  //@ assert \at(x,L) == x - 1;

}
