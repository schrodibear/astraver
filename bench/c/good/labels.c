

/*@ ensures \result == 0
  @*/
int f1() {
  int x=0;
  goto l1;
  x=1;
 l1: return x;
}

int f2() {
  goto l1;
 l2: goto l3;
 l1: goto l2;
 l3: return 0;
}

int f3(int x) {
  if (x==0) { 
    goto l2; 
    l1 : x = 1;  
  } else {
    goto l1;
    l2 : x = 2;
  }
  return x;
}

  
