
typedef struct purse {
  int balance;
} purse;

//@ predicate purse_inv(purse *p) { \valid(p) && p->balance >= 0 }

/*@ requires purse_inv(p) && s >= 0
  @ assigns p->balance
  @ ensures purse_inv(p) && p->balance == \old(p->balance) + s 
  @*/
void credit(purse *p,int s) {
  p->balance = p->balance + s;
}

/*@ (* requires purse_inv(p) && s >= 0 *)
  @ assigns p->balance
  @ (* ensures purse_inv(p) && p->balance == \old(p->balance) + s *)
  @*/
void f(purse *p,int s) {
  p->balance = p->balance + s;
}

/*@ requires purse_inv(p) && 0 <= s <= p->balance
  @ assigns p->balance
  @ ensures purse_inv(p) && p->balance == \old(p->balance) - s
  @*/
void withdraw(purse *p,int s) {
  p->balance = p->balance - s;
}


/*@ requires purse_inv(p1) && purse_inv(p2)  
  @ assigns p1->balance, p2->balance
  @ ensures \result == 0
  @*/
int test1(purse *p1, purse *p2) {
    p1->balance = 0;
    credit(p2,100);
    return p1->balance;
}

/*@ assigns \nothing
  @ ensures \fresh(\result) && purse_inv(\result) && \result->balance == 0
  @*/
purse *new_purse() { 
  purse* p = (purse*) malloc(1 * sizeof(purse));
  p->balance = 0;
  return p;
}

/*@ ensures \result == 150
  @*/
int test2() {
  purse *p1 = new_purse();
  purse *p2 = new_purse();
  credit(p1,100);
  credit(p2,200);
  withdraw(p1,50);
  withdraw(p2,100);
  return p1->balance + p2->balance;
}

/*
void main() {
  purse *p = new_purse();
  test1(p,p);
}
*/
