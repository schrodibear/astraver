
struct A
{
    int n;
    int* a;
};

typedef struct A A;

/*@
    requires \valid(x);
    requires (x->n >= 0) && \valid(x->a+(0..x->n-1));

    assigns x->a[i];

    behavior assign_sth:
        assumes 0 <= i < x->n;
        assigns x->a[i];

    behavior assign_nth:
        assumes i < 0 || i >= x->n;
        assigns \nothing;

    complete behaviors;
    disjoint behaviors;
*/
void foo(A* x, int i)
{
    if (i >= 0 && i < x->n)
        x->a[i] = 0;
}

/*@
    requires \valid(x);
    requires \valid(y);
    requires (x->n >= 0) && \valid(x->a+(0..x->n-1));
    requires (y->n >= 0) && \valid(y->a+(0..y->n-1));
    requires \separated(x, y, x->a + (0..x->n-1), y->a + (0..y->n-1));
*/
void bar(A* x, A* y, int i)
{
    foo(x, i);
    //@ assert y->a == \at(y->a, Pre);
    // assert smoke: 0 == 1;
}
