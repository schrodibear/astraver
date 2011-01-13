/* run.config
 */

int f () {
  int x = 1;
  L:
  x = 2;
  //@ assert \at(x,L) == x - 1;
 }

/*
Local Variables:
compile-command: "make labels2.opt"
End:
*/
