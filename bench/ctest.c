
/*

C test file

*/

int x;
short y;
void z;

int f(int a, int b) 
/*@ pre x = 0
    writes x
    post result = a + b */;

/* void g(int a) { int i = 0; x = i; } */

int main() 
/*@ x >= 0 */ 
{
  x = 0 + 2.3;
  for (y = 0; y < 10; ++y)
    /*@ invariant x = y and y <= 10 variant 10-y */
    x = x + 1;
} 
/*@ x = 10 */

