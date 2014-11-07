

struct union_find;

/* logic int Repr(union_find u, int a); */

/* predicate Same(union_find u, int a, int b) = Repr(u,a) == Repr(u,b); */

/* logic uint NumClasses(union_find u); */


/*@ requires sz >= 1;
  @ assigns \nothing;
  @ ensures forall i, repr(result, i) = i;
  @*/
union_find create(uint sz);


/*@ requires 0 <= a < sz;
  @ assigns \nothing;
  @ ensures \result == repr(u, a);
  @*/
int find(union_find u, int a);

/*@ requires 0 <= a < sz;
  @ requires 0 <= b < sz;
  @ behavior already_same_class:
  @   assumes same(u,a,b);
  @   assigns \nothing;
  @ behavior true_union:
  @   assumes ! same(u,a,b);
  @   assigns u;
  @   ensures forall int s,t; same(u,s,t) <==> 
  @    (  \old(same(u,s,t)) 
  @    || (\old(same(u,s,x)) && \old(same(u,t,y)) ) 
  @    || (\old(same(u,s,y)) && \old(same(u,t,x)) ));
  @   ensures NumClasses(u) == \old(NumClasses(u)) - 1;
  @*/
void union(union_find u, int a, int b);

/*@ assigns \nothing;
  @ ensures \result == NumClasses(u);
  @*/
unit get_num_classes(union_find u);

