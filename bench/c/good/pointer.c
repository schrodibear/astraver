
/* C tests with pointers */

/*@ requires \valid(x)
  @ ensures *x == 1 && \result == 0 */
int f(int *x) {
  *x = 0;
  return (*x)++;
} 

/*@ requires \valid(x)
  @ ensures *x == 1 && \result == 1 */
int f2(int *x) {
  *x = 0;
  return ++(*x);
} 

int* r;


/*@ requires \valid(r)
  @ ensures *r == 1 */
int g() { 
  return f(r); 
}

void * malloc(int);

/*@ ensures *r == 1 */
int g2() { 
  r = (int *)malloc(sizeof(int));
  return f(r); 
}

/*@ ensures \result == 1 */
int h() { int z = 0; return f(&z) + z; }

