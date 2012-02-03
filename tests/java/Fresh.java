

class Fresh {

    /*@ allocates \result;
      @*/
    static Fresh create();

    test() {
        Fresh f = create ();
        //@ assert this != f;
    }
}