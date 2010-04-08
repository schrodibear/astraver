
// a stupid lemma
//@ lemma stupid : 1+1 == 2;

//@ ensures \result == x;
int f(int x) {
  //@ assert x > 0;
  return x;
}
