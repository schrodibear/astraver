
/*

C test file

*/

int x;

/*@ requires x == 0 ensures x == 10 */ 
void main() 
{
  int i = 0;
  for (i = 0; i < 10; ++i)
    /*@ invariant x == i && i <= 10 variant 10-i */
    x = x + 1;
} 

