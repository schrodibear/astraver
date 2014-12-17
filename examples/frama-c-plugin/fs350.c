/* run.config
*/
/*@ requires 0 <= argc <= 10;
  requires \valid(argv + (0..argc-1)); */
int main(int argc, char **argv) {
  int i;
  char *t[10];
  /*@ loop invariant 0 <= i;
    @*/
  for(i = 0; i < argc; i++) t[i] = argv[i];
  return 0;
}

/*
Local Variables:
compile-command: "LC_ALL=C make fs350"
End:
*/
