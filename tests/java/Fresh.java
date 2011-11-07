

class Fresh {

    /*@ ensures \fresh(\result);
      @*/
    static Fresh create();

    test() {
        Fresh f = create ();
        //@ assert this != f;
    }
}