
/*@ ensures \result == 18 */
int f1(void) {
  return 010+0x0A;
}

int f2(void){
  int i =0xFFFF0000;
  return i;
}
