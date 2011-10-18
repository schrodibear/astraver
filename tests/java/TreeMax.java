
//@+ TerminationPolicy = user

/*@ axiomatic integer_max {
  @   logic integer max(integer x, integer y);
  @   axiom max_is_ge : \forall integer x y; max(x,y) >= x && max(x,y) >= y;
  @   axiom max_is_some : \forall integer x y; max(x,y) == x || max(x,y) == y;
  @ }
  @*/

class Int {
    //@ ensures \result == max(x,y);
    public static int max(int x, int y);
}

/*@ axiomatic Mem {
  @   predicate mem{L}(int x, Tree t);
  @   axiom mem_null{L}: \forall int x; ! mem(x,null);
  @   axiom mem_root{L}: \forall Tree t; t != null ==>
  @     mem(t.value,t);
  @   axiom mem_root_eq{L}: \forall int x, Tree t; t != null ==>
  @     x==t.value ==> mem(x,t);
  @   axiom mem_left{L}: \forall int x, Tree t; t != null ==>
  @     mem(x,t.left) ==> mem(x,t);
  @   axiom mem_right{L}: \forall int x, Tree t; t != null ==>
  @     mem(x,t.right) ==> mem(x,t);
  @   axiom mem_inversion{L}: \forall int x, Tree t;
  @     mem(x,t) ==> t != null &&
  @       (x==t.value || mem(x,t.left) || mem(x,t.right));
  @ }
  @*/

/* attempt to prove termination, not succesful yet */
/* axiomatic Finite {
  @   predicate has_size{L}(Tree t, integer s);
  @   axiom has_size_null{L}: has_size(null,0);
  @   axiom has_size_non_null{L}: \forall Tree t; t != null ==>
  @     \forall integer s1 s2;
  @     has_size(t.left,s1) && has_size(t.right,s2) ==>
  @     has_size(t,s1+s2+1) ;
  @   axiom has_size_inversion{L}: \forall Tree t, integer s;
  @     has_size(t,s) ==>
  @       (t == null && s == 0) ||
  @       (t != null && \exists integer s1 s2;
  @            has_size(t.left,s1) && has_size(t.right,s2) &&
  @            0 <= s1 && 0 <= s2 && s == s1+s2+1) ;
  @   predicate size_decreases{L}(Tree t1, Tree t2) =
  @     \exists integer s1 s2; has_size(t1,s1) && has_size(t2,s2) && s1 > s2;
  @ }
  @*/

class Tree {

    int value;
    Tree left;
    Tree right;

    /*@ // requires \exists integer s; has_size(this,s);
      @ // decreases this for size_decreases;
      @ ensures mem(\result,this) &&
      @   \forall int x; mem(x,this) ==> \result >= x;
      @*/
    int tree_max() {
        int m = value;
        if (left != null) m = Int.max(m,left.tree_max());
        if (right != null) m = Int.max(m,right.tree_max());
        return m;
    }

}

