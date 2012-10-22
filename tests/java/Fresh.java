

class Fresh {

    /*@ allocates \result;
      @ ensures \fresh(\result);
      @*/
    static Fresh create() {
        return new Fresh ();
    }

    void test () {
        Fresh f = create ();
        //@ assert this != f;
    }
}




/*
Local Variables:
compile-command: "make Fresh.why3ide"
End:
*/


