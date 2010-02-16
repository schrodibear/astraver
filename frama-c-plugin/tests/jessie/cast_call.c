/* run.config
*/

#pragma SeparationPolicy(Regions)

/*@ requires \valid(c);
  @ ensures \result == c;
  @*/
char* f(char *c) {
  return c;
}  
  
void g() {
  int i;
  char *c = f((char*)&i);
  *c = 0;
  //@assert i == 0;
}

/* 
Local Variables:
compile-command: "LC_ALL=C make cast_call"
End:
*/
