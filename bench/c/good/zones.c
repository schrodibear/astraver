

typedef struct S {
  int *x;
  int *y;
} S;

S *a,*b;


int f() {
  a = b;
  return *(a->x) + *(b->y);
}
