
#include "list.h"

/*@ requires
  @   \valid(l)
  @ ensures 
  @   \result <=> cyclic(l) 
  @*/
int cyclic(list l) {
  list l1 = l;
  list l2;
  if (!l1) return 0;
  l2 = l1->tl;
  /*@ invariant (\exists plist pl1; lpath(l,pl1,l1)) &&
    @           (\exists plist pl2; lpath(l,pl2,l2)) &&
    @           (\exists plist pl12; lpath(l1,pl12,l2))
    @*/
  while (l1 != l2) {
    if (!l1 || !l2 || !l2->tl) return 0;
    l1 = l1->tl;
    l2 = l2->tl->tl;
  }
  return 1;
}

