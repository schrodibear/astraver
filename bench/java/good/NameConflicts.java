
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


/*
Local Variables: 
compile-command: "make NameConflicts.io"
End: 
*/
