
#pragma SeparationPolicy(none)

/* #include <stdlib.h> */
void *malloc(unsigned int size);


typedef struct Str {int x; } *str;


/*@ allocates \result;
  @ assigns \nothing;
  @ ensures \valid(\result) && \fresh(\result,sizeof(*\result));
  @*/
str create(void) {
  str s;
  s = (str)malloc(sizeof(struct Str));
  return s;
}

/*@ requires \valid(this);
  @*/
void test(str this) {
  str f;
  f = create ();
  //@ assert this != f;
}

void smoke_detector() {
  str s1 = create ();
  str s2 = create ();
  //@ assert 0 == 1;
}

/*
Local Variables:
compile-command: "LC_ALL=C make fresh2_sep.why3ide"
End:
*/