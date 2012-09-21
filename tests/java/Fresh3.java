
//@+ SeparationPolicy = None

class Int { int f; }

class Fresh3 {

  Int i;

/*@ assigns this.i;
  @ allocates this.i;
  @ ensures this.i != null && \fresh(this.i);
  @*/
void create() {
    this.i = new Int();
}

/*@ requires f != null && this.i != null && this != f;
  @*/
void test(Fresh3 f) {
  f.create();
  //@ assert this.i != f.i;
}

static void smoke_detector() {
    Fresh3 s1, s2;
    s1 = new Fresh3();
    s2 = new Fresh3();
    s1.create();
    s2.create();
    //@ assert 0 == 1;
}

}

/*
Local Variables:
compile-command: "LC_ALL=C make Fresh3.why3"
End:
*/
