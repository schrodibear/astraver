
// #pragma SeparationPolicy(none)

typedef struct Str {int x; } *str;


/*@ ensures \fresh(\result,sizeof(*\result));
  @*/
str create(void);

//@ requires \valid(this);
void test(str this) {
  str f;
  f = create ();
  //@ assert this != f;
}

void smoke_detector() {
  str s1 = create ();
  str s2 = create ();
  //@ assert \false;
}

/* 
Local Variables:
compile-command: "LC_ALL=C make fresh2.why3ml"
End:
*/