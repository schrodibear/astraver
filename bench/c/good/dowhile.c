
/*

C test file

*/

int x;
int i;

/*@ requires x >= 0  ensures x == 10 */ 
void main() 
{
  x = 0;
  i = 10;
  /*@ invariant x == 10 - i && i >= 0 variant i */
  do {
    x = x + 1;
    i = i - 1;
  } while (i > 0);
} 


