/* Frama-C BTS 0063

Status: closed

*/

int f () {
  int x = 1;
  L:
  x = 2;
  //@ assert \at(x,L) == x - 1;
  return x;
 }


/* 
Local Variables:
compile-command: "LC_ALL=C frama-c -jessie bts0063.c"
End:
*/
