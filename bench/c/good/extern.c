int x = 5;
/*@ ensures \result == 5 */
int f() {
  void *x;
  {
    extern int x;
    return x;
  }
}
