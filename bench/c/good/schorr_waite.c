
/* Schorr-Waite algorithm */

typedef struct struct_node {
  unsigned int m :1;
  unsigned int c :1;
  struct struct_node *l, *r;
} * node;

/*@ predicate in_list(node p,plist stack) */

/*@ predicate pair_in_list(node p1,node p2, plist stack) */

/*@ predicate reachable (node p1, node p2) reads p1->r,p1->l */

/* predicate stkOk (node p, plist stack) reads p->c,p->l,p->r,\old(p->l),\old(p->r)*/

/*@ predicate clr_list (node p, plist stack) reads p->c,p->l,p->r*/

#define null ((void*)0)
/*@ requires 
  @   \forall node x; reachable (root,x) => ! x ->m 
  @ ensures 
  @   (\forall node x; \old (x->l) == x->l && \old (x->r) == x->r) &&
  @   (\forall node x; reachable (root,x) => x->m) &&
  @   (\forall node x; ! reachable (root,x) => x->m == \old(x->m))
*/
void schorr_waite(node root) {
  node t = root;
  node p = null;
  /*@invariant
    @ (\forall node x; \old(reachable(root,x)) =>
    @       (reachable(t,x) || reachable(p,x)))&&
    @ \exists plist stack;
    @   clr_list (p,stack) &&
    @   (\forall node p; in_list (p,stack) => p->m) &&
    @   (\forall node x; \old(reachable(root,x)) =>
    @       (reachable(t,x) || reachable(p,x)))&&
    @   (\forall node x; \old(reachable(root,x)) && x->m =>
    @       reachable(t,x) || 
    @       (\forall node y ; in_list(y,stack)=> reachable(y->r,x))) &&
    @  (\forall node x; !in_list(x,stack) =>  
            (x->r == \old(x->r) && x->l == \old(x->l))) &&
    @  (\forall node p1; (\forall node p2;
              pair_in_list(p1,p2,stack) => 
	          (p2->c => \old(p2->l) == p2->l && \old(p2->r) == p1)
                  &&
	          (!p2->c => \old(p2->l) == p1 && \old(p2->r) == p2->r)))
  */
  /*      (\forall node p1; (\forall node p2;
              pair_in_list(p1,p2,stack) => 
	          (\old(p2->l) == (p2->c ? p2->l : p1)) &&
	          (\old(p2->r) == (p2->c ? p1 : p2->r))))
  */
  while (p != null || (t != null && ! t->m)) {
    if (t == null || t->m) {
      if (p->c) {
	/* pop */
	node q = t;
	t = p;
	p = p->r;
	t->r = q;
      } else {
	/* swing */
	node q = t;
	t = p->r;
	p->r = p->l;
	p->l = q;
	p->c = 1;
      }
    } else {
      /* push */
      node q = p;
      p = t;
      t = t->l;
      p->l = q;
      p->m = 1;
      p->c = 0;
    }
  }
}
