typedef struct Node {
    int value;

    int childrenCount;
    struct Node *children;
} Node;

typedef struct Tree {
    Node *root;

    int nodesCount;
    Node *nodes;
} Tree;

/*@
  requires \valid(t);
  requires \valid(t->nodes+(0..t->nodesCount - 1));
  assigns t->nodes[0 .. t->nodesCount - 1].value;
 */
void zeroValues(Tree *t) {
    /*@ loop invariant 0 <= i;
      @ loop variant t->nodesCount - i;
      @*/
    for (int i = 0; i < t->nodesCount; ++i) {
        t->nodes[i].value = 0;
    }
}
