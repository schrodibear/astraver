
#include "list.h"

/*@ ensures if \result then cyclic(l1) else !cyclic(l1) */
int cyclic(list l1) {
  list l2;
  if (!l1) return 0;
  l2 = l1->tl;
  while (l1 != l2) {
    if (!l1 || !l2 || !l2->tl) return 0;
    l1 = l1->tl;
    l2 = l2->tl->tl;
  }
  return 1;
}

