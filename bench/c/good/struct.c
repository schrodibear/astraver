
typedef struct T {
  int x;
  int y;
} T;

/*@ requires \valid(t2) && t2->x == 0
  @ assigns t2->x
  @ ensures \result == 1 && t2->x == 2 && t2->y == \old(t2->y)
  @*/
int f(T* t2) {
  t2->x++; 
  return t2->x++;
}

struct S { int z; T t; } s;
struct S *ps;

struct S *pps[] = { (void*)0 };

/*@ requires \valid(ps)
  @ ensures \result == 1
  @*/
int g() {
  T *p;
  ps = &s;
  pps[0] = ps;
  p = &(s.t);
  ps->t.x = 1;
  return s.t.x;
}
