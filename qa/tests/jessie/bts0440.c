/* Frama-C BTS 0440

Status: open

  
*/

int fact(int n) {
  int r = 1 ;
  while ( n > 0 ) {
    //@ assert n > 0 ;
  before:
    r *= n-- ;
    //@ assert r == \at(r*n,before) ;
  }
  return r ;
}



/* 
Local Variables:
compile-command: "make bts0440"
End:
*/



