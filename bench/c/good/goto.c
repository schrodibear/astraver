

/*@ ensures \result == 0
  @*/
int f1() {
  int x=0;
  goto l1;
  x=1;
 l1: return x;
}

  
