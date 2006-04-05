
#include "tree.h"

/*@ requires valid_tree(t)
  @ ensures \result != \null => (path(t,\result) && \result->node == v) */
tree brute_force_search(tree t, int v) {
  tree u;
  if (t == NULL) return NULL;
  if (t->node == v) return t;
  u = brute_force_search(t->left, v);
  if (u != NULL) return u;
  return brute_force_search(t->right, v);
}

/*@ requires valid_tree(t) && bst(t)
  @ ensures \result != \null => (path(t,\result) && \result->node == v) */
tree binary_search(tree t, int v) {
  if (t == NULL) return NULL;
  if (t->node == v) return t;
  if (v < t->node) 
    return binary_search(t->left, v);
  else
    return binary_search(t->right, v);
}
