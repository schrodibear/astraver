
typedef struct struct_list {
  int hd;
  struct struct_list * tl;
} *list;

#define nil ((void*)0)

/*@ predicate is_list(list l) reads l->tl */
/*@ predicate llist(list l, plist pl) reads l->tl */
/*@ predicate cyclic(list l) reads l->tl */

/*@ logic plist rev(plist pl) */
/*@ logic plist app(plist l1, plist l2) */
/*@ predicate disjoint(plist l1, plist l2) */

/*@ logic StorePointerPair store_pointer_pair(list l) reads l->tl */



/* @ inutile : predicate eq_list(plist l1, plist l2) */

#if 0
/* axioms for Simplify */

/* axiom ll_order_wf : well_founded(ll_order) */

/*@ axiom is_list_llist_ax :
    \forall list p;
     is_list(p) => \exists plist l; llist(p,l) */

/*@ axiom llist_function_ax :
    \forall plist l1; \forall plist l2; \forall list p;
    llist(p,l1) => llist(p,l2) => eq_list(l1,l2) */

/*@ axiom eq_list_def : \forall plist x; \forall plist y;
    x==y => eq_list(x,y) */
#endif
