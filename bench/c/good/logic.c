
/*@ logic int f1(int t[], int x) reads t[..] */

/*@ axiom ax_f1 : \forall int t[], int x; f1(t,x) == t[x] */

void test_f1() {
  int t[2];
  t[0] = 0;
  //@ assert f1(t,0) == 0
}


/*@ logic int f2(int t[], int x) { t[x] } */

void test_f2() {
  int t[2];
  t[0] = 0;
  // @ assert f2(t,0) == 0
}


/*@ predicate p1(int t[], int x, int v) reads t[..] */

/*@ axiom ax_p1 : \forall int t[], int x, int v; p1(t,x,v) <=> t[x]==v */

void test_p1() {
  int t[2];
  t[0] = 0;
  //@ assert p1(t,0,0)
}



/*@ predicate p2(int t[], int x, int v) { t[x]==v } */

void test_p2() {
  int t[2];
  t[0] = 0;
  //@ assert p2(t,0,0)
}

