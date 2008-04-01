
//@+ CheckArithOverflow = no


class NoCreditException extends Exception {

    public NoCreditException() { }

}

public class Purse {
    
    private int balance;
    //@ invariant balance_non_negative: balance >= 0;

    /*@ requires true;
      @ assigns \nothing;
      @ ensures balance == 0;
      @*/
    public Purse() {
        balance = 0;
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
      @ ensures s <= \old(balance) && balance == \old(balance) - s;
      @ behavior amount_too_large:
      @   assigns \nothing;
      @   signals (NoCreditException) s > \old(balance) ;
      @*/
    public void withdraw(int s) throws NoCreditException {
        if (balance >= s)
            balance = balance - s;
        else
            throw new NoCreditException();
    }

    //@ ensures \result == balance;
    public int getBalance() {
        return balance;
    }

}

