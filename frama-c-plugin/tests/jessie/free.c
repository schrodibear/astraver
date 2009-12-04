
void free(void *p);

/*@
  requires \valid(p);
  assigns *p;
*/
int f(int*p) {
  free(p);
}

/*@
  requires \valid(q);
  ensures \valid(q); */
int main(int* q) {
  return f(q);
}
