
//@+ NonNullByDefault = alllocal

class C { 
    public int x;
}

class StaticTyping {

    C a;

    void m1(C c) {
	a = null; // bug jessie : OP non generee
	// C b = c; // b pas marque "non null"...
	a.x = 0; // ..du coup : PO inutile
    }


    void m2(C c) {
	m1(c);
    }

    byte[] buffer;

    byte[] getBuffer() { return buffer; }

    void m3() {
	byte[] cmd_apdu = getBuffer();
	
	if (cmd_apdu.length >= 10) cmd_apdu[9] = 0;
    }

}
    


    
