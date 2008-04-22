
//@+ NonNullByDefault = alllocal

class C { 
    public int x;
}

class StaticTyping {

    C a;

    void m1(C c) {
	a = null; // bug jessie : OP non generee
	C b = c; // b pas marque "non null"...
	b.x = 0; // ..du coup : PO inutile
    }


    void m2(C c) {
	m1(c);
    }

}
    


    
