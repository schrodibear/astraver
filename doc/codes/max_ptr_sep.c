/*@ requires \valid(i) && \valid(j);
  @ requires r == \null || \valid(r);
  @ ensures *i == \old(*i) && *j == \old(*j);
  @*/
int max(int *r, int* i, int* j) {
  if (!r) return -1;
  *r = (*i < *j) ? *j : *i;
  return 0;
}
