

typedef struct {
  int x;
  int y;
} T;


/*@ requires \valid(t)
  @ ensures \true
  @*/
int f(T* t) {
  return t->x;
}
