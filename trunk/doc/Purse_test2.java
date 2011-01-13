    /*@ public normal_behavior
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

