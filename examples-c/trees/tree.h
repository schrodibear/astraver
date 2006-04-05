
struct struct_tree {
  int node;
  struct struct_tree * left;
  struct struct_tree * right;
};

typedef struct struct_tree* tree;

#define NULL ((void*)0)

/* @ type ptree */

/* @ logic ptree nil() */ 

/* @ logic ptree cons(tree p) */

/* @ logic ptree new(int n, ptree t1, ptree t2) */

/* @ logic int tree_depth(ptree t) */

/* @ predicate disjoint(ptree t1, ptree t2) */

/* @ axiom disjoint_nil1 : \forall ptree t; disjoint(t,nil()) */

/* @ axiom disjoint_nil2 : \forall ptree t; disjoint(nil(),t) */

/* @ predicate finite(tree t) reads t->right, t->left */

/* @ predicate cyclic(tree t) reads t->right, t->left */

/* @ type Depth */

/* @ logic Depth depth(tree t) reads t->right, t->left */

/*@ predicate valid_tree(tree t) reads t->left,t->right */

/*@ axiom valid_tree_def: 
  @   \forall tree t; 
  @   valid_tree(t) <=>
  @    ( t == \null || 
  @      (\valid(t) && valid_tree(t->left) && valid_tree(t->right)))
  @*/

/*@ predicate path(tree t1, tree t2) 
  @   reads t1->left, t1->right, t2->left, t2->right 
  @*/

/*@ axiom path_refl: 
  @   \forall tree t; path(t,t) 
  @*/

/*@ axiom path_left: 
  @   \forall tree t1, tree t2, tree t3;
  @   (path(t2,t3) && t1->left == t2) => path(t1,t3) 
  @*/

/*@ axiom path_right: 
  @   \forall tree t1, tree t2, tree t3;
  @   (path(t2,t3) && t1->right == t2) => path(t1,t3) 
  @*/

/* Binary Search Trees */

/*@ predicate bst(tree t) */



