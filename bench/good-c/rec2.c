
/* C recursive function */

int f(int x) /*@ x >= 0 variant x */ {
  if (x == 0) return 0;
  return f(x - 1);
} /*@ result = 0 */
