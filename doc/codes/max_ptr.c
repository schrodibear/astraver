/*@ requires \valid(i) && \valid(j);
  @ requires r == \null || \valid(r);
  @ assigns *r;
  @ behavior zero:
  @   assumes r == \null;
  @   assigns \nothing;
  @   ensures \result == -1;
  @ behavior normal:
  @   assumes \valid(r);
  @   assigns *r;
  @   ensures *r == ((*i < *j) ? *j : *i);
  @   ensures \result == 0;
  @*/
int max(int *r, int* i, int* j) {
  if (!r) return -1;
  *r = (*i < *j) ? *j : *i;
  return 0;
}
