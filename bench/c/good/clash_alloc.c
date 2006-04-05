
typedef struct T {
    int alloc;
} S;

/*@ requires \valid(p) */
int f(S* p)
{
  return p->alloc;
}




