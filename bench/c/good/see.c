
/* Side effect in expressions (Bart Jacobs' tricky example) */

int b;
int b1; 
int b2;

/*@ assigns b 
  @ ensures \result == b && b == 1 - \old(b) */
int f() {
  b = 1 - b;
  return b;
}

/*@ ensures b1 == 0 && b2 == 1 */
void k() {
  b = 1;
  b1 = f() + (1 - f());
  b2 = (1 - f()) * f();
}

