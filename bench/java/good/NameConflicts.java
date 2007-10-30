
class C1 {
    int i;
    
    void setI(int i) {
	this.i = i;
    }

}

class C2 {
    
    /*@ behavior normal:
      @   ensures \result == 0;
      @*/
    int m() {
	int result = 0;
	return 0;
    }
}

class C3 {

    int field;

    int field() { return field; }

}

/*
Local Variables: 
compile-command: "make NameConflicts.io"
End: 
*/
