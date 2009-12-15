
void free(void *p);

/*@
  requires \valid(p);
  assigns \nothing;
  ensures ! \valid(p);
*/
void f(int*p) {
  free(p);
  //@ assert must_not_be_proved: \valid(p);
}

/*@
  requires \valid(q);
  */
int main(int* q) {
  f(q);
  return 0;
}


/* BTS 0338: free(NULL) should be allowed */
void free_null() {
  int *p = (void*)0;
  free(p);
}
