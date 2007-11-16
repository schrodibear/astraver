    /*@ public normal_behavior
      @   modifiable balance;
      @   ensures balance == 0;
      @*/
    Purse() {
        balance = 0;
    }

    /*@ public normal_behavior
      @   requires s >= 0;
      @   modifiable balance;
      @   ensures balance == \old(balance)+s;
      @*/
    public void credit(int s) {
        balance += s;
    }

    /*@ public normal_behavior
      @   requires s >= 0 && s <= balance;
      @   modifiable balance;
      @   ensures balance == \old(balance) - s;
      @*/
    public void withdraw(int s) {
        balance -= s;
    }

