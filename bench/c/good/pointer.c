
/* C tests with pointers */

/*@ ensures *x == 1 && \result == 0 */
int f(int *x) {
  *x = 0;
  return (*x)++;
}

int* r;

/*@ ensures *r == 1 */
int g() { return f(r); }

/*@ ensures \result == 1 */
int h() { int z = 0; return f(&z) + z; }
