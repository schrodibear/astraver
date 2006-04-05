struct S { int a; int b[5]; int c[5]; };

struct L { struct S q; struct S *p; int r[10]; };

struct S s0;
struct L l;

/* no alias between s0 and l.q */
/*@ ensures \result == 1 */
int f() {
  s0.a = 1;
  l.q.a = 2;
  return s0.a;
}

/* s0 and l.p are the same structure (alias) */
/*@ ensures \result == 1 */
int f2() {
  s0.b[2] = 1;
  l.p = &s0;
  return l.p->b[2];
}

/* internal separation of s0.b and s0.c */
//@ ensures \result == 1
int f3() {
  s0.b[2] = 1;
  s0.c[2] = 2;
  return s0.b[2];
}
