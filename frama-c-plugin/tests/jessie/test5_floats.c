/* run.config
 */

#pragma JessieFloatModel(strict)


/*@ axiomatic Truncate {
  @   logic integer truncate(real x);
  @ }
  @*/


void f() {
  
  float x = 1.0f, y = 0.0f;
  
  /*@ loop invariant x-y == 1.0;
    @ loop assigns x,y;
    @ loop variant (16777216 - truncate(y));  
    @*/
  while (y != x) {y = x ; x += 1.0f;}
  //@ assert x == y == 0x2.0p24;
}



/* 
Local Variables:
compile-command: "LC_ALL=C make test5_floats"                            
End:
*/
