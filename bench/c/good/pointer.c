
/* C tests with pointers */

/*@ requires \valid(x)
  @ ensures *x == 1 && \result == 0 */
int f(int *x) {
  *x = 0;
  return (*x)++;
} 

int* r;


#if 0
/*@ requires \valid(r)
  @ ensures *r == 1 */
int g() { 
  return f(r); 
}

/*@ ensures *r == 1 */
int g2() { 
  r = (int *)malloc(sizeof(int));
  return f(r); 
}

/*@ ensures \result == 1 */
int h() { int z = 0; return f(&z) + z; }
#endif

