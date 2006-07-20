

/*@ ensures \result == 0
  @*/
int f1() {
  int x=0;
  goto l1;
  x=1;
 l1: return x;
}


/*@ ensures x == 0 => \result == 0
  @*/
int f2(int x) {
  if (x==0) goto l1;
  x=1;
 l1: return x;
}


/*@ ensures x == 9 <=> \result == 10
  @*/
int f3(int x) {
  if (x==0) goto l1;
  x++;
  if (x==10) goto l1;
  x=1;
 l1: return x;
}

  
