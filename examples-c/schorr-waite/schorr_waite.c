
/* Schorr-Waite algorithm */

typedef struct struct_node {
  unsigned int m :1;
  unsigned int c :1;
  struct struct_node *l, *r;
} * node;

/*@ logic plist cons(node p, plist l) */

/*@ logic var_type mkvar_type(node p, node t) reads p->m,p->c,p->l,p->r*/

/*@ predicate in_list(node p,plist stack) */

/*@ predicate pair_in_list(node p1, node p2, plist stack) */

/*@ predicate isreachable(node p1, node p2) reads p1->r,p1->l */

/*@ predicate unmarked_reachable(node p1, node p2) reads p1->r,p1->l,p1->m */

/*@ predicate clr_list(node p, plist stack) reads p->c,p->l,p->r*/

/*@ predicate reachable_elements(node p, node t, plist l) reads p->l,p->r*/ 


#define NULL ((void*)0)

/*@ requires 
  @   (\forall node x; 
  @      x != \null && isreachable(root,x) => \valid(x) && ! x ->m)
  @   && \exists plist l; reachable_elements(root,root,l)
  @ ensures 
  @   (\forall node x; \old(x->l) == x->l && \old(x->r) == x->r) 
  @   &&
  @   (\forall node x; \valid(x) && isreachable(root,x) => x->m) 
  @   &&
  @   (\forall node x; ! isreachable(root,x) => x->m == \old(x->m))
*/
void schorr_waite(node root) {
  node t = root;
  node p = NULL;
  /*@ invariant
    @ (\forall node x; 
    @   (\old(isreachable(root,x)) => (isreachable(t,x) || isreachable(p,x))))
    @ &&
    @ (\forall node x; x != \null => 
    @   ((isreachable(t,x) || isreachable(p,x)) => \old(isreachable(root,x)))) 
    @ &&
    @ \exists plist stack;
    @  clr_list(p,stack) 
    @  &&
    @  (I1 :: \forall node p; in_list(p,stack) => p->m) 
    @  &&
    @  (I2 :: \forall node x; 
    @     \valid(x) && \old(isreachable(root,x)) && !x->m =>
    @      unmarked_reachable(t,x) || 
    @      (\exists node y; in_list(y,stack) && unmarked_reachable(y->r,x))) 
    @  &&
    @  (I3 :: \forall node x; !in_list(x,stack) =>  
    @      (x->r == \old(x->r) && x->l == \old(x->l))) 
    @  &&
    @  (I4 :: \forall node p1; (\forall node p2;
    @      pair_in_list(p1,p2,cons(t,stack)) => 
    @        (p2->c => \old(p2->l) == p2->l && \old(p2->r) == p1)
    @           &&
    @        (!p2->c => \old(p2->l) == p1 && \old(p2->r) == p2->r)))
    @  &&
    @  (I5 :: \forall node x; 
    @      ! \old(isreachable(root,x)) => x->m == \old(x->m)) 
    @  &&
    @  (I6 :: \forall node x; 
    @      x != \null && \old(isreachable(root,x)) => \valid(x)) 
    @  variant mkvar_type(p,t) for order_mark_m_and_c_and_stack
  */
  /*
      (\forall node p1; (\forall node p2;
              pair_in_list(p1,p2,stack) => 
	          (\old(p2->l) == (p2->c ? p2->l : p1)) &&
	          (\old(p2->r) == (p2->c ? p1 : p2->r))))
  */
  while (p != NULL || (t != NULL && ! t->m)) {
    if (t == NULL || t->m) {
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
