
/*@ requires n > 0;
  @ ensures \valid(\result+(0..n-1));
  @*/
char *f(int n) {
  char *i = (char*) malloc(n);
  return i;
}

/* 
Local Variables:
compile-command: "LC_ALL=C make allocation"
End:
*/
