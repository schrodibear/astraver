

int y;

/*@ ensures \result == 0 && y == \old(y) */
int g() {
  int y; y = 0 ;
  return y;
}
