/* Frama-C BTS 0040

yields:

File "wholeprogram.jc", line 53, characters 15-26: typing error: type
float_P[..] expected instead of real

still open
  
*/




typedef struct {float k;} las;
void g (float * y);
void f (las *c) { g(&(c->k)); }


/* 
Local Variables:
compile-command: "LC_ALL=C frama-c -jessie bts0040.c bts0040.h"
End:
*/



