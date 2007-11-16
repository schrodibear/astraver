class Purse {
    
    int balance;
    //@ public invariant balance >= 0; 

    /*@ public normal_behavior
      @   requires s >= 0;
      @*/
    public void credit(int s) {
        balance += s;
    }

    /*@ public normal_behavior
      @   requires s >= 0 && s <= balance;
      @*/
    public void withdraw(int s) {
        balance -= s;
    }
}

