
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
/*@ predicate eq_list(plist l1, plist l2) */
/*@ predicate disjoint(plist l1, plist l2) */

/*@ logic StorePointerPair store_pointer_pair(list l) reads l->tl */

