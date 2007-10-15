
class NoCreditException extends Exception {

}

public class Purse {
    
    public int balance;

    //@ invariant balance_non_negative: balance >= 0;

    /*@ behavior created:
      @   assigns \nothing;
      @   ensures balance == 0;
      @*/
    public Purse() {
	balance = 0;
    }

    /*@ requires s >= 0;
      @ behavior done:
      @   assigns balance;
      @   ensures balance == \old(balance)+s;
      @*/
    public void credit(int s) {
	balance += s;
    }

    /*@ requires s >= 0 && s <= balance;
      @ behavior done:
      @   assigns balance;
      @   ensures balance == \old(balance) - s;
      @*/
    public void withdraw(int s) {
	balance -= s;
    }
    
    /*@ requires s >= 0;
      @ behavior done:
      @   assigns balance;
      @   ensures s <= \old(balance) && balance == \old(balance) - s;
      @ behavior amount_too_large:
      @   assigns \nothing;
      @   signals (NoCreditException) s > \old(balance) ;
      @*/
    public void withdraw2(int s) throws NoCreditException {
	if (balance >= s) {
	    balance = balance - s;
	}
	else {
	    throw new NoCreditException();
	}
    }

    /*@ requires p1 != null && p2 != null && p1 != p2;
      @ behavior ok:
      @   assigns p1.balance,p2.balance;
      @   ensures \result == 0;
      @*/
    public static int test(Purse p1, Purse p2) {
	p1.balance = 0;
	p2.credit(100);
	return p1.balance;
    }


    /*@ behavior ok:
      @   assigns \nothing;
      @   ensures \result == 150;
      @*/
    public static int test2() {
	Purse p1 = new Purse();
	Purse p2 = new Purse();
	p1.credit(100);
	p2.credit(200);
	p1.withdraw(50);
	p2.withdraw(100);
	return p1.balance+p2.balance;
    }

    /*@ requires p1 != null && p2 != null && p1 != p2;
      @ behavior ok:
      @   assigns p2.balance;
      @   ensures \result == \old(p1.balance);
      @*/
    public static int test3(Purse p1,Purse p2) {
	p2.credit(100);
	return p1.balance;
    }

    /*@ requires p != null;
      @ behavior ok:
      @   assigns p.balance ;
      @   ensures \result <==> (\old(p.balance) >= 1000);
      @*/
    public static boolean test4(Purse p) {
	try {
	    p.withdraw2(1000);
	    return true;
	}
	catch (NoCreditException e) { 
	    return false; 
	}
    }

    
    /* @ behavior not_ok:
      @   ensures false
      @*/
    /*
    public static void main(String argv[]) {
	Purse p = new Purse();
	// erroneous 
	p.withdraw(10); 
	p.credit(10);
    }
*/    

}


/*
Local Variables: 
compile-command: "make Purse.io"
End: 
*/
