
/* Schorr-Waite algorithm */

typedef struct struct_node {
  unsigned int m :1;
  unsigned int c :1;
  struct struct_node *l, *r;
} * node;

/*@ predicate in_list(node p,plist stack) */

/*@ predicate reachable (node p1, node p2) reads p1->r,p1->l */

/*@ predicate stkOk (node p, plist stack) reads p->r,p->l,p->c*/

/*@ predicate clr_list (node p, plist stack) reads p->c,p->l,p->r*/

/*@ predicate all_in_list (plist stack)*/

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
    @\exists plist stack;
    @clr_list (p,stack) &&
    @all_in_list (stack) &&
    @\forall node x; \old(reachable(root,x))=>
    @(reachable(t,x) || reachable(p,x))&&
    @(\forall node x; \old(reachable(root,x)) && x->m=>
    @reachable(t,x) || \forall node y ; in_list(y,stack)=> reachable(y->r,x))&&
    @
    @\forall node x;!in_list(x,stack)=>(x->r == \old(x->r) && x->l == \old(x->l))
    @&& stkOk(t,stack) 
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
