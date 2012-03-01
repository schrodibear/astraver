



/*@ ensures \valid(\result) && \fresh(\result,sizeof(int));
  @*/
int* f();


void g() {
   int* p;
   p = f();
   *p = 0;
}

/* 
Local Variables:
compile-command: "LC_ALL=C make fresh.why3ml"
End:
*/
