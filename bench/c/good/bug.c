typedef struct U { int t2[5]; int t2bis[5]; int *p2; } las2;
typedef struct V { int t1[5]; int t1bis[5]; int *p1; las2 * pp; } las;
las u,v,w;
las2 z;
las2 y1[5];
las2 y2[10];

/* predicate separation_intern_struct_U(las2* p) reads p->t2, p->t2bis */

/* axiom sep_U : 
  \forall las2 *p; \valid(p) => separation_intern_struct_U(p) */


/*@ requires \valid(x) */
void f(struct U *x) { x->t2[0] = 1; *u.p1 = 1; *z.p2 = 2; }
