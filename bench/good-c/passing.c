
/*

C test file

*/

int t[];

void g(int* x) { *x = 0; } /*@ x = 0 */

int * r;

int g2() { g(r); return *r; } /*@ result = 0 */

void f(int x[]) /*@ array_length(x) = 1 */ { 
  x[0] = 1;
} /*@ x[0] = 1 */

void main() /*@ array_length(t) = 1 */ {
  f(t);
} /*@ t[0] = 1 */


  
