
typedef struct struct_tree {
  int node;
  struct struct_tree * rt;
  struct struct_tree * lt;
} *tree;

#define NULL ((void*)0)

/*@ type ptree */

/*@ logic ptree nil() */ 

/*@ logic ptree cons(tree p) */

/*@ logic ptree new(int n, ptree t1, ptree t2) */

/*@ logic int tree_depth(ptree t) */

/*@ predicate disjoint(ptree t1, ptree t2) */

/*@ axiom disjoint_nil1 : \forall ptree t; disjoint(t,nil()) */

/*@ axiom disjoint_nil2 : \forall ptree t; disjoint(nil(),t) */

/*@ predicate finite(tree t) reads t->rt, t-> lt */

/*@ predicate cyclic(tree t) reads t->rt, t-> lt */

/*@ type Depth */

/*@ logic Depth depth(tree t) reads t->rt, t-> lt */

/*@ predicate is_tree(tree t) 
  { 
    ((t->rt == NULL) or is_tree(t->rt)) and (t->lt == NULL or is_tree(t->lt))
    and is_tree(disjoint(cons(l->rt), cons(l->lt)) 
  }
*/
