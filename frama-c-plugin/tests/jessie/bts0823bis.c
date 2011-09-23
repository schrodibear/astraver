#pragma SeparationPolicy(regions)

struct _elem {
    struct _elem *next;
};

/*@ axiomatic leibniz_law {
    predicate Dummy{L}(integer dummy) = \true;
    axiom eax0: \forall struct _elem *p,*q;
	Dummy(0) && \valid(p) && p == q ==> p->next == q->next;
}
*/

//@ requires \valid(a) && \valid(b) && a == b;
void ftest(struct _elem *a, struct _elem *b) {
    b->next = (void*)0;
    //@ assert \at(b->next,Pre) == b->next;
} 

