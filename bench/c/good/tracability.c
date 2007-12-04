
// memory safety VC
int f1(int *p) { return *p; }


// loop invariant VCs (initially true, preserved)
void f2() {
  int i = 10;
  //@ invariant i == 5 //intentionally false
  while (i > 0) i--;
}

/*
Local Variables: 
compile-command: "make tracability.gui"
End: 
*/
