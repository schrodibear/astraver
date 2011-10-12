
int x;

/*@ requires \at(x,Pre) <= 2000; */
int f (void) {

  int y = x;
  
  { y++; x++; }
  /*@ ensures y == \at(x, Old) + 1 == \at(x,Pre) + 2; */
  y++;

}
