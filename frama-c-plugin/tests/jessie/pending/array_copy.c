
struct S {
  int i;
  int *p;
};

struct T {
  struct S fs[3][2];
};

struct U {
  struct T ft[2];
};

struct S s;
struct T t;
struct U u;

/*@ requires \valid(lu.ft[1].fs[2][1].p);
  @ ensures \result == 1;
  @ */
int f(struct U lu) {
  lu.ft[1].fs[2][1].p = &lu.ft[1].fs[2][1].i;
  lu.ft[1].fs[2][1].i = 0;
  return *lu.ft[1].fs[2][1].p;
}

/* 
Local Variables:
compile-command: "LC_ALL=C make array_copy"
End:
*/
