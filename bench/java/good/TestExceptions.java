

class C {

    void m1() { }

    void m2() {
        try {
            m1();
        } catch(Exception e) { }
    }
}



/*
Local Variables: 
compile-command: "make TestExceptions"
End: 
*/
