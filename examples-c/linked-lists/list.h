
typedef struct struct_list {
  int hd;
  struct struct_list * tl;
} *list;

#define NULL ((void*)0)

/*@ predicate is_list(list l) reads l->tl */
/*@ predicate cyclic(list l) reads l->tl */

/*@ logic plist rev(plist pl) */
/*@ logic plist app(plist l1, plist l2) */
/*@ predicate disjoint(plist l1, plist l2) */

/*@ logic StorePointerPair store_pointer_pair(list l) reads l->tl */


/* axioms for Simplify */

/* axiom ll_order_wf : well_founded(ll_order) */

/*@ logic plist nil() */ 
/*@ logic plist cons(list p, plist l) */

/*@ predicate lpath(list p1, plist l, list p2) reads p1->tl */

/*@ axiom app_nil_end_ax :
  @ \forall plist l; l == app(l,nil()) 
  @*/

/*@ axiom Path_null_ax : 
  @ \forall list p; lpath(p,nil(),p)
  @*/

/*@ axiom Path_cons :
  @ \forall list p1; \forall plist l; \forall list p2;
      \valid(p1) => lpath(p1->tl,l,p2) => lpath(p1,cons(p1,l),p2)
*/

/** [(llist t p l)]: there is a (finite) linked list starting from pointer [p]
    using links in store [t], and this list of pointers is [l] */
/*@ predicate llist(list p, plist l) { lpath(p,l,\null) } */ 

/*@ axiom is_list_llist_ax :
    \forall list p;
     is_list(p) => \exists plist l; llist(p,l) */

/* axiom llist_function_ax :
    \forall plist l1; \forall plist l2; \forall list p;
    llist(p,l1) => llist(p,l2) => eq_list(l1,l2) */

/*@ axiom disjoint_nil1 :
  \forall plist l; disjoint(l,nil()) */

/*@ axiom disjoint_nil2 :
  \forall plist l; disjoint(nil(),l) */
   

