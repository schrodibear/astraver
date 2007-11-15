

class C {

    /*@ behavior exc:
      @   signals (Exception) true;
      @*/
    void throwException() {
	throw new Exception();
    }

    void m() {
	throwException();
    }

}



/*
Local Variables: 
compile-command: "make TestExceptions"
End: 
*/
