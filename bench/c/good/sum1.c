
/*

C test file

*/

int x;

/*@ requires x == 0 assigns x ensures x == 10 */ 
void main() 
{
  int i = 0;
  /*@ invariant x == i && i <= 10 variant 10-i */
  for (i = 0; i < 10; ++i)
    x++;
} 

