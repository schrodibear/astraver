
typedef struct {
  int x;
  int y;
} T;

/*@ requires \valid(t) && t->x == 0
  @ assigns t->x
  @ ensures \result == 1 && t->x == 2 && t->y == \old(t->y)
  @*/
int f(T* t) {
  t->x++; 
  return t->x++;
}

struct S { int z; T t; } s;
struct S *ps;

/*@ requires \valid(s) && \valid(s.t) && \valid(ps)
  @ ensures \result == 1
  @*/
int g() {
  T *p;
  ps = &s;
  p = &s.t;
  ps->t.x = 1;
  return s.t.x;
}
