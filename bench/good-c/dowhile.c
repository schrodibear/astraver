
/*

C test file

*/

int x;
int i;

int main() 
/*@ x >= 0 */ 
{
  x = 0;
  i = 10;
  do {
    x = x + 1;
    i = i - 1;
  }
    /*@ invariant x = 10 - i and i >= 0 variant i */
  while (i > 0);
} 
/*@ x = 10 */

