
/* Side effect in expressions (Bart Jacobs' tricky example) */

int b;
int b1; 
int b2;

int f() {
  b = 1 - b;
  return b;
} /*@ result = b and b = 1 - b@ */


void k() {
  b = 1;
  b1 = f() + (1 - f());
  b2 = (1 - f()) * f();
} /*@ b1 = 0 and b2 = 1 */

