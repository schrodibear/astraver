#pragma SeparationPolicy(Regions)

/*@ axiomatic Conversion {
  @   axiom little_endian_low_byte_short{L}: 
  @     \forall short *s; *(char*)s == *s % 256;
  @   
  @ axiom little_endian_high_byte_short{L}: 
  @   \forall short *s; *((char*)s+1) == *s / 256; }
  @*/

/*@ axiomatic Div {
  @  axiom div_modulo:
  @   \forall integer i; i == 256 * (i / 256) + i % 256; }
  @*/

/*@ requires \valid(x) && \valid(y);
  @ ensures *x == \old(*y) && *y == \old(*x);
  @*/
void swap(char *x, char *y) {
  char tmp = *x;
  *x = *y;
  *y = tmp;
}

/*@ requires \valid(s);
  @ ensures *s == 256 * (\old(*s) % 256) + (\old(*s) / 256);
  @*/
void reverse_endian(short *s) {
  char *c = (char*)s;
  swap(c,c+1);
}

/*
Local Variables:
compile-command: "LC_ALL=C make -j reverse_endian2"
End:
*/


/* logic integer little_endian_short{L}(short *s) =
   @   *(char*)s + *((char*)s+1) * 256;
   @
   @ logic integer big_endian_short{L}(short *s) =
   @   *((char*)s+1) + *(char*)s * 256;
   @*/
