
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
