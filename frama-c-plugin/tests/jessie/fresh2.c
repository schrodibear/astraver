
// #pragma SeparationPolicy(none)

typedef struct Str {int x; } *str;


/*@ ensures \fresh(\result);
  @*/
str create();

//@ requires \valid(this);
void test(str this) {
  str f = create ();
  //@ assert this != f;
}

void smoke_detector() {
  str s1 = create ();
  str s2 = create ();
  //@ assert \false;
}
