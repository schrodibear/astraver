
/*

C test file

*/

int x;

void main() 
/*@ x = 0 */ 
{
  int i = 0;
  for (i = 0; i < 10; ++i)
    /*@ invariant x = i and i <= 10 variant 10-i */
    x = x + 1;
} 
/*@ x = 10 */

