
/*

C test file

*/

int x;
int i;

int f(int a, int b) 
/*@ pre x = 0
    writes x
    post result = a + b */;

/* void g(int a) { int i = 0; x = i; } */

int main() 
/*@ x >= 0 */ 
{
  x = -0;
  i = 10;
  do {
    x = x + 1;
    i = i - 1;
  }
  /*@ invariant x = 10 - i and i >= 0 variant 10-i */
  while (i > 0);
} 
/*@ x = 10 */

