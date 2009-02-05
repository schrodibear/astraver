//@+ CheckArithOverflow = no

class NoCreditException extends Exception {

    public NoCreditException() { }

}

public class Purse {
    
    static NoCreditException noCreditException = new NoCreditException();

    private int balance;
    //@ invariant balance_positive: balance > 0;

    /*@ requires amount > 0;
      @ assigns balance;
      @ ensures balance == amount;
      @*/
    public Purse(int amount) {
        balance = amount;
    }

    /*@ requires s >= 0;
      @ assigns balance;
      @ ensures balance == \old(balance) + s;
      @*/
    public void credit(int s) {
        balance += s;
    }

    /*@ requires s >= 0;
      @ assigns balance;
      @ ensures s < \old(balance) && balance == \old(balance) - s;
      @ behavior amount_too_large:
      @   assigns \nothing;
      @   signals (NoCreditException) 
      @         s >= \old(balance) ;
      @*/
    public void withdraw(int s) throws NoCreditException {
        if (s < balance)
            balance = balance - s;
        else
            throw noCreditException;
    }


    /*@ requires p != null && p != this && s >= 0;
      @ behavior transfer_ok:
      @   ensures 
      @       balance == \old(balance) - s &&
      @       p.balance == \old(p.balance) + s &&
      @       \result == balance;
      @ behavior transfer_failed: 
      @   signals (NoCreditException) 
      @       balance == \old(balance) &&
      @       p.balance == \old(p.balance);
      @*/
    public int transfer_to(Purse p, int s) throws NoCreditException {
	p.credit(s);
	withdraw(s);
	return balance;
    }
	
}
