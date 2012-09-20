
//@+ SeparationPolicy = None

class Fresh2 {

    int x;

    /*@ assigns \nothing;
      @ ensures \fresh(this);
      @*/
    Fresh2 ();

    /*@ assigns \nothing;
      @ allocates \result;
      @ ensures \result != null && \fresh(\result);
      @*/
    static Fresh2 create() {
        return new Fresh2();
    }

    void test() {
        Fresh2 f;
        f = create ();
        //@ assert this != f;
    }

    static void smoke_detector() {
        Fresh2 s1 = create ();
        Fresh2 s2 = create ();
        //@ assert 0 == 1;
    }

}


/*
Local Variables:
compile-command: "LC_ALL=C make Fresh2.why3ide"
End:
*/
