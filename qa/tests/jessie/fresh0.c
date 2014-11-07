

int *x;

/*@ allocates x;
  @ assigns x;
  @ ensures \valid(x) && \fresh(x,sizeof(int*));
  @*/
void test1();

typedef struct S {int *f; } *st;


/*@ requires \valid(s);
  @ allocates s->f;
  @ assigns s->f;
  @ ensures \valid(s->f) && \fresh(s->f,sizeof(int*));
  @*/
void test2(st s);

/*
Local Variables:
compile-command: "LC_ALL=C make fresh0.why3ide"
End:
*/
