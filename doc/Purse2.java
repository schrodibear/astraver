/*@ assigns balance;
  @ ensures balance == 0;
  @*/
Purse() {
    balance = 0;
}

/*@ requires s >= 0;
  @ assigns balance;
  @ ensures balance == \old(balance)+s;
  @*/
public void credit(int s) {
    balance += s;
}

/*@ requires 0 <= s <= balance;
  @ assigns balance;
  @ ensures balance == \old(balance) - s;
  @*/
public void withdraw(int s) {
    balance -= s;
}

