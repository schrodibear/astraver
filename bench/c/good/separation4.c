

typedef struct S {
  int a;
  int b[5];
}
S;



S x,y;

/*@ predicate p(S a) { a.b[0] >= 0 } */

/*@ requires p(x) */
void f() {
  x.b[0] = 0;
  y.b[1] = 1;
}


