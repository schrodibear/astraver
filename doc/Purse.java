class Purse {
    
    int balance;
    //@ invariant balance_non_negative: balance >= 0; 

    
    /*@ ensures balance == 0;
      @*/
    Purse() {
        balance = 0;
    }

    /*@ requires s >= 0;
      @ ensures balance == \old(balance)+s;
      @*/
    public void credit(int s) {
        balance += s;
    }

    /*@ requires s >= 0 && s <= balance;
      @ ensures balance == \old(balance)-s;
      @*/
    public void withdraw(int s) {
        balance -= s;
    }
}

