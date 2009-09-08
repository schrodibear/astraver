
//@ ensures \result == (void*)0;
int* f() {
  int* p;
  p = (void*)0;
  return p;
}

#ifndef NULL
#define NULL ((void*)0)
#endif /* NULL */

//@ ensures \result == \null;
int* g() {
  int* p;
  p = NULL;
  return p;
}

/* 
Local Variables:
compile-command: "LC_ALL=C make null"
End:
*/
