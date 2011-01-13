class NoCreditException extends Exception {

    /*@ assigns \nothing;
      @*/
    NoCreditException() {}

}

class Purse {

    /*@ requires s >= 0;
      @ assigns balance;
      @ ensures s <= \old(balance) && balance == \old(balance) - s;
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

}



