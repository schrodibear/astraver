
/* C tests with pointers */

int f(int *x) /*@ */ {
  *x = 0;
  return (*x)++;
} /*@ x = 1 and result = 0 */

int* r;

int g() { return f(r); } /*@ r = 1 */

int h() { int z = 0; return f(&z) + z; } /*@ result = 1 */
