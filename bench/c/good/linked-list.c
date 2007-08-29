
typedef struct struct_list {
  int hd;
  struct struct_list * tl;
} *list;

#define NULL ((void*)0)

/*@ predicate is_list(list p) reads p->tl */

/*@ axiom is_list_def : 
     \forall list p; 
     is_list(p) <=> (p == NULL || (\valid(p) && is_list(p->tl))) */

/*@ logic int length(list p) reads p->tl */

/* @ axiom length_null : length((list)NULL) == 0 */

/*@ axiom length_nonneg : \forall list p; is_list(p) => length(p) >= 0 */

/*@ axiom length_cons : 
     \forall list p; 
     is_list(p) => p != NULL => length(p) == length(p->tl) + 1 */

/*@ requires is_list(p)
  @ ensures  \result != NULL => \result->hd == v
  @*/
list search(list p, int v) {
  /*@ invariant is_list(p)
      variant   length(p) */
  while (p != NULL && p->hd != v) p = p->tl;
  return p;
}
