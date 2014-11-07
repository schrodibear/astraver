
#define NULL		((void*)0)

struct _cell { struct _cell *nxt; }; 

// define linked-list property:
/*@ axiomatic a1 {
    logic boolean isList{L}(struct _cell *b,struct _cell *f);
    axiom a2{L}:
	\forall struct _cell *b, struct _cell *f; isList(b,f) <==>
	    f == NULL || 
	    \base_addr(f) == \base_addr(b) && isList(b,f->nxt);
}
*/

