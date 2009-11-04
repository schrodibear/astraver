/* Frama-C BTS 0026

Status: closed

Fixed in Why 2.22
  
*/

# pragma JessieIntegerModel(math)

/*@ behavior b1:
  @   assumes n > 0;
  @ behavior b2:
  @   assumes n <= 0;
  @ complete behaviors;
  @ disjoint behaviors;
  @*/
int f1(int n) {
  return n+1;
}

/*@ requires x * y < 0;
  @ behavior b1:
  @   assumes x >= 0;
  @ behavior b2:
  @   assumes y >= 0;
  @ complete behaviors b1,b2; 
  @ disjoint behaviors b1,b2;  
  @*/
int f2(int x, int y) {
  return x+y;
}


/* 
Local Variables:
compile-command: "LC_ALL=C frama-c -jessie bts0026.c"
End:
*/



