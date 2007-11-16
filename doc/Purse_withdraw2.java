class NoCreditException extends Exception {

    /*@ public normal_behavior
      @   modifiable \nothing;
      @*/
    NoCreditException() {}
}

class Purse {

    /*@ public behavior
      @   requires s >= 0;
      @   modifiable balance;
      @   ensures s <= \old(balance) && balance == \old(balance) - s;
      @   signals (NoCreditException) 
      @     s > \old(balance) && balance == \old(balance);
      @*/
    public void withdraw2(int s) throws NoCreditException {
        if (balance >= s) {
            balance -= s;
        }
        else {
            throw new NoCreditException();
        }
    }
}

