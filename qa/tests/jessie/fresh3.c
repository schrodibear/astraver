
#pragma SeparationPolicy(none)

/* #include <stdlib.h> */

/*@ allocates \result;
  @ assigns \nothing;
  @ ensures \valid((char*)\result) && \fresh(\result,size);
  @*/
void *malloc(unsigned int size);

typedef struct Str {int *x; } *str;


/*@ requires \valid(s);
  @ allocates s->x;
  @ assigns s->x;
  @ ensures \valid(s->x) && \fresh(s->x,sizeof(int*));
  @*/
void create(str s) {
  s->x = (int*)malloc(sizeof(int*));
}

// #if 0

str f;

/*@ requires \valid(f) && \valid(this) && \valid(this->x);
  @ requires this != f;
  @*/
void test(str this) {
  create (f);
  //@ assert this->x != f->x;
}

str s1, s2;

/*@ requires \valid(s1) && \valid(s2);
  @*/
void smoke_detector() {
  create (s1);
  create (s2);
  //@ assert 0 == 1;
}

// #endif

/*
Local Variables:
compile-command: "LC_ALL=C make fresh3.why3ide"
End:
*/
