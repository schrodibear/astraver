
/*@ requires \valid(p)
  @ assigns *p
  @ ensures *p == 1
  @*/
void g(int *p) {
  *p = 1;
}

int x = 45;

/*@ assigns x
  @ ensures x == 1
  @*/
void f1() {
  x = 1;
}

/*@ assigns x
  @ ensures x == 1
  @*/
void f2() {
  g(&x);
}


int t[3] = {1,2,3};

/*@ requires \valid(p) && \valid( *p)
  @ assigns **p
  @ ensures **p == 2
  @*/
void h(int **p) {
  **p = 2;
}

/*@ ensures t[0] == 2 && t[1] == 2 */
void f3() {
  h(&t);
}
