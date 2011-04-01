
//@ logic integer sum_upto(integer n) = n*(n+1) / 2;

/*@ lemma sum_rec: \forall integer n; n >=0 ==>
  @     sum_upto(n+1) == sum_upto(n)+n+1;
  @*/

/*@ requires x >= 0;
  @ requires x <= 1000;
  @ decreases x;
  @ ensures \result == sum_upto(x);
  @*/
long sum(int x) {
  if (x == 0) return 0;
  else return x + g (x-1);
}


/*@ ensures \result == 36; 
  @*/
long main () {
  long i = sum(8);
  return i;
}



/*@ decreases 101-n ;
  @ behavior less_than_101:
  @   assumes n <= 100;
  @   ensures \result == 91;
  @ behavior greater_than_100:
  @   assumes n >= 101;
  @   ensures \result == n - 10;
  @*/
int f91(int n) {
  if (n <= 100) {
    return f91(f91(n + 11));
  }
  else
    return n - 10;
}
