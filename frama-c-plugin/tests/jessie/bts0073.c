/*@
axiomatic myaxioms{

    predicate myrelation(int p,int q);
    logic int mylogic{L}(int * p);

    axiom myaxiom{L} :
    \forall int * p, q; \at(myrelation(mylogic(p),q),L);

}
@*/


