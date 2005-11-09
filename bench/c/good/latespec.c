

void f(int *p) {
  *p = 0;
}

/*@ requires \valid(p) 
  @ assigns *p
  @*/
void f(int *p);
