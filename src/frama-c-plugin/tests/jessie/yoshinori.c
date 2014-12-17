typedef struct Yoshinori { 
  int i; 
} yoshinori;

/*@
  @ axiomatic test1 {
  @   logic yoshinori func;
  @   predicate pred1{L} = \at(func, L).i > 0;
  @ }
  @*/

