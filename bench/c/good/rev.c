
/* in-place list reversal */

#include "list.h"

/*@ requires is_list(p)
  @ (* assigns ??? *)
  @ ensures \exists plist l0; llist(\result, l0) && \old(llist(p, rev(l0)))
  @*/
list rev(list p) {
  list r = p;
  p = nil;
  /*@ invariant 
        \exists plist lp; \exists plist lr;
          llist(p, lp) && llist(r, lr) && disjoint(lp, lr) &&
          \forall plist l; 
            \old(llist(p, l)) => eq_list(app(rev(lr), lp), rev(l))
    @ variant r for ll_order (* ??? *) */
  while (r != nil) {
    list q = r;
    r = r->tl;
    q->tl = p;
    p = q;
  }
  return p;
}

/* test */

#if 1
#include <stdio.h>

void print(list l) {
  if (l == nil) 
    printf("nil\n");
  else {
    printf("%d :: ", l->hd);
    print(l->tl);
  }
}

int main() {
  /* 1::2::3::nil */
  struct struct_list l[3];
  list r;
  l[0].hd = 1;
  l[0].tl = &l[1];
  l[1].hd = 2;
  l[1].tl = &l[2];
  l[2].hd = 3;
  l[2].tl = nil;
  print(l);
  r = rev(l);
  print(r);
}
#endif
