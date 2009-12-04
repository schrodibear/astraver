

//@ lemma mean_property2: \forall integer l, h; l <= h  ==>  l <= (l+h)/2 <= h;

//@ lemma div2pos: \forall integer x; x >= 0  ==>  x >= x/2 >= 0;
//@ lemma div2neg: \forall integer x; x <= 0  ==>  x <= x/2 <= 0;

//@ ensures l <= \result <= h;
int foo(int l, int h) {
  return (l+h)/2;
}

/*
Main() {
  int a = foo(maxint, maxint);
}
*/
