/*@ predicate P(int *a) = a[0] == a[1];
  @*/

//@ axiomatic A { logic integer f(int n); }

//@ lemma L: \forall int* a; P(a) ==> f(a[0]) == f(a[1]);

//@ lemma L2: \forall int *a; a[1] == 0;


//@ ensures \result == 4;
int f() { 
  int *a;
  int r;
  r = a[0]; 
  return r;
}
