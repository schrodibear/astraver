    /*@ public normal_behavior
      @   ensures \result == 150;
      @*/
    public static int test1() {
        Purse p = new Purse();
        p.credit(100);
        p.withdraw(50);
        p.credit(100);
        return p.balance;
    }
