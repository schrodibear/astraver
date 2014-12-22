//#define NULL 0

struct s {
  int a, b;
};

typedef unsigned long int size_t;

// It seems standard malloc/free functions don't need explicit
// specification as the special treatment for them is
// hardcoded in Jessie
extern void* malloc(size_t size);

extern void free(void *p);


/*@ ensures \valid(\result) && (\result)->a == a &&
  @         \offset_min(\result) == 0;
 */
struct s *pack_in_struct(int a)
{
  struct s *result;
  result = malloc(2 * sizeof (struct s));
  result = &result[1];
  result->a = a;
  return result;
}


/*@ requires \valid(p) &&
  @          \offset_min(p) == 0;
  @ ensures \result == p->a;
 */
int get_a_and_free(struct s *p)
{
  int result = p->a;
  free(p);
  return result;
}

/*@ ensures \result == v;
 */
int main(int v)
{
  return get_a_and_free(pack_in_struct(v));
}
