/* Frama-C BTS 0102

Status: open



The following annotated code can not be proved by ATPs.

Function f() needs an invariant on global var v :
    //@ global invariant aa: \valid(&v.c);
that should normally be generated automatically.

Function f2() needs a type invariant :
    //@ type invariant Tt(las* l) = \valid(&(l->c)); but this type invariant is visibly not taken into account in the Why generated file (predicate Tt does exist but is not axiomatized).

    */

typedef struct { int c; } las;
las v;
//@ requires \valid(p);
void g(int * p);
void f(){ g(&v.c); }
//@ requires \valid(x);
void f2(las * x){ g(&(x->c)); }

/*
Local Variables:
compile-command: "LC_ALL=C frama-c -jessie bts0102.c"
End:
*/
