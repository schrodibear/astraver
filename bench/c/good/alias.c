
/*@ requires \valid(x) && \valid(y) 
  @ ensures \result == 0
  @*/
int f(int *x, int *y) {
  *x = 0;
  *y = 1;
  return *x;
}


int  p[1];

int g() {
  return f(p,p);
}

