
#pragma JessieTerminationPolicy(user)

#define NULL (void*)0

//@ ensures \result == \max(x,y);
int max(int x, int y);

typedef struct Tree *tree;
struct Tree {
  int value;
  tree left;
  tree right;
};

/* not accepted by Why3 (termination not proved) 
  @ predicate mem(int x, tree t) =
  @  (t==\null) ? \false : (x==t->value) || mem(x,t->left) || mem(x,t->right);
  @*/

/*@ axiomatic Mem {
  @   predicate mem{L}(int x, tree t);
  @   axiom mem_null{L}: \forall int x; ! mem(x,\null);
  @   axiom mem_root{L}: \forall tree t; t != \null ==>
  @     mem(t->value,t);
  @   axiom mem_root_eq{L}: \forall int x, tree t; t != \null ==>
  @     x==t->value ==> mem(x,t);
  @   axiom mem_left{L}: \forall int x, tree t; t != \null ==>
  @     mem(x,t->left) ==> mem(x,t);
  @   axiom mem_right{L}: \forall int x, tree t; t != \null ==>
  @     mem(x,t->right) ==> mem(x,t);
  @   axiom mem_inversion{L}: \forall int x, tree t;
  @     mem(x,t) ==> t != \null &&
  @       (x==t->value || mem(x,t->left) || mem(x,t->right));
  @ }
  @*/

/*@ axiomatic WellFormedTree {
  @   predicate has_size{L}(tree t, integer s);
  @   axiom has_size_null{L}: has_size(\null,0);
  @   axiom has_size_non_null{L}: \forall tree t; \valid(t) ==>
  @     \forall integer s1,s2;
  @     has_size(t->left,s1) && has_size(t->right,s2) ==>
  @     has_size(t,s1+s2+1) ;
  @   axiom has_size_inversion{L}: \forall tree t, integer s;
  @     has_size(t,s) ==>
  @       (t == \null && s == 0) ||
  @       (\valid(t) && \exists integer s1,s2;
  @            has_size(t->left,s1) && has_size(t->right,s2) &&
  @            0 <= s1 && 0 <= s2 && s == s1+s2+1) ;
  @  predicate size_decreases{L}(tree t1, tree t2) =
  @    \exists integer s1,s2; has_size(t1,s1) && has_size(t2,s2) && s1 > s2;
  @   predicate valid_tree{L}(tree t) =
  @     \exists integer s; has_size(t,s);
  @ }
  @*/

/*@ requires t != \null && valid_tree(t);
  @ // decreases t for size_decreases;
  @ ensures mem(\result,t) && \forall int x; mem(x,t) ==> \result >= x;
  @*/
int tree_max(tree t) {
  int m = t->value;
  if (t->left != NULL) m = max(m,tree_max(t->left));
  if (t->right != NULL) m = max(m,tree_max(t->right));
  return m;
  }



/*
Local Variables:
compile-command: "make tree_max.why3ide"
End:
*/
