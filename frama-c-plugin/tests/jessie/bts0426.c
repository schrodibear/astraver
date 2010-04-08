typedef struct {
	int index;
    char b;
} T_S;

//@ predicate P0{L}(T_S *s) = (s->b==1) ;

/*@ axiomatic Index {

logic integer f_index{L}(integer old, T_S *new);

// XXX ceci fait crasher Jessie

axiom Index1{L}:
    \forall integer old, T_S *new;
        P0{L}(new) ==> f_index{L}(old, new) == old;
}*/

