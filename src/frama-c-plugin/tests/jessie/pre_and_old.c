


#pragma JessieIntegerModel(math)


int y;

//@ logic integer f{L}(integer n) = n+y;

/*@ ensures \result == \old(f(x));
  @ ensures \result == f{Old}(x);
  @ ensures \result == \at(f(x),Pre);
  @*/
int g(int x) {
  int tmp = y;
  y = 12;
  return x+tmp;
}
  

