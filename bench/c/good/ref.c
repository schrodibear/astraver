


/*@ requires \valid(p)
  @ assigns *p
  @ ensures *p == 1
  @*/
void g(int *p) {
  *p = 1;
}

//@ ensures \result == 1
int f() {
  int i;
  g(&i);
  return i;
}
